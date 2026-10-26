import V185TrunkScan20Chunk061

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_377784 : List Nat := [2, 1, 2, 1, 2, 6, 1, 5]
def baseStart_377784 : Nat := 118140960795 + 377784 * 2 ^ 59
def prefixEnd_377784 : Nat := 4983230072969 + 3 ^ 40 * 377784 * 2
def baseEnd_377784 : Nat := 57476970541705230240773

theorem tailTrace_377784 : CollatzResearch.WordTrace tailWord_377784 prefixEnd_377784 57476970541705230240773 := by
  unfold tailWord_377784
  simp only [CollatzResearch.WordTrace]
  refine ⟨6889457231680281607790203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9185942975573708810386937 6889457231680281607790203)
  ·
    refine ⟨10334185847520422411685305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6889457231680281607790203 10334185847520422411685305)
    ·
      refine ⟨7750639385640316808763979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10334185847520422411685305 7750639385640316808763979)
      ·
        refine ⟨11625959078460475213145969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7750639385640316808763979 11625959078460475213145969)
        ·
          refine ⟨8719469308845356409859477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11625959078460475213145969 8719469308845356409859477)
          ·
            refine ⟨408725123852126081712163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8719469308845356409859477 408725123852126081712163)
            ·
              refine ⟨613087685778189122568245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408725123852126081712163 613087685778189122568245)
              ·
                refine ⟨57476970541705230240773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 613087685778189122568245 57476970541705230240773)
                ·
                  rfl

theorem cell20_377784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_377784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377784 prefixEnd_377784 := by exact prefixLift 377784
  have htrace : WordTrace (prefixWord ++ tailWord_377784) baseStart_377784 baseEnd_377784 := by
    simpa [prefixWord, tailWord_377784, baseEnd_377784] using wordTrace_append hprefix tailTrace_377784
  have hstable : (prefixWord ++ tailWord_377784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377784).length < 2 ^ (prefixWord ++ tailWord_377784).sum := by decide
  have hdescent : baseEnd_377784 < baseStart_377784 := by decide
  rcases family_descends (prefixWord ++ tailWord_377784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377842 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_377842 : Nat := 118140960795 + 377842 * 2 ^ 59
def prefixEnd_377842 : Nat := 4983230072969 + 3 ^ 40 * 377842 * 2
def baseEnd_377842 : Nat := 172457384405525266788749

theorem tailTrace_377842 : CollatzResearch.WordTrace tailWord_377842 prefixEnd_377842 172457384405525266788749 := by
  unfold tailWord_377842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445257474287609780297945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9187353264766959414127853 3445257474287609780297945)
  ·
    refine ⟨2583943105715707335223459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3445257474287609780297945 2583943105715707335223459)
    ·
      refine ⟨3875914658573561002835189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2583943105715707335223459 3875914658573561002835189)
      ·
        refine ⟨363366999241271344015799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3875914658573561002835189 363366999241271344015799)
        ·
          refine ⟨545050498861907016023699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363366999241271344015799 545050498861907016023699)
          ·
            refine ⟨817575748292860524035549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545050498861907016023699 817575748292860524035549)
            ·
              refine ⟨306590905609822696513331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 817575748292860524035549 306590905609822696513331)
              ·
                refine ⟨459886358414734044769997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306590905609822696513331 459886358414734044769997)
                ·
                  refine ⟨172457384405525266788749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459886358414734044769997 172457384405525266788749)
                  ·
                    rfl

theorem cell20_377842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_377842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377842 prefixEnd_377842 := by exact prefixLift 377842
  have htrace : WordTrace (prefixWord ++ tailWord_377842) baseStart_377842 baseEnd_377842 := by
    simpa [prefixWord, tailWord_377842, baseEnd_377842] using wordTrace_append hprefix tailTrace_377842
  have hstable : (prefixWord ++ tailWord_377842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377842).length < 2 ^ (prefixWord ++ tailWord_377842).sum := by decide
  have hdescent : baseEnd_377842 < baseStart_377842 := by decide
  rcases family_descends (prefixWord ++ tailWord_377842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377870 : List Nat := [4, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_377870 : Nat := 118140960795 + 377870 * 2 ^ 59
def prefixEnd_377870 : Nat := 4983230072969 + 3 ^ 40 * 377870 * 2
def baseEnd_377870 : Nat := 172470164368481613855301

theorem tailTrace_377870 : CollatzResearch.WordTrace tailWord_377870 prefixEnd_377870 172470164368481613855301 := by
  unfold tailWord_377870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1722756392631124987901383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9188034094032666602140709 1722756392631124987901383)
  ·
    refine ⟨2584134588946687481852075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1722756392631124987901383 2584134588946687481852075)
    ·
      refine ⟨3876201883420031222778113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584134588946687481852075 3876201883420031222778113)
      ·
        refine ⟨2907151412565023417083585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3876201883420031222778113 2907151412565023417083585)
        ·
          refine ⟨2180363559423767562812689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2907151412565023417083585 2180363559423767562812689)
          ·
            refine ⟨1635272669567825672109517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2180363559423767562812689 1635272669567825672109517)
            ·
              refine ⟨613227251087934627041069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1635272669567825672109517 613227251087934627041069)
              ·
                refine ⟨229960219157975485140401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 613227251087934627041069 229960219157975485140401)
                ·
                  refine ⟨172470164368481613855301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229960219157975485140401 172470164368481613855301)
                  ·
                    rfl

theorem cell20_377870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_377870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377870 prefixEnd_377870 := by exact prefixLift 377870
  have htrace : WordTrace (prefixWord ++ tailWord_377870) baseStart_377870 baseEnd_377870 := by
    simpa [prefixWord, tailWord_377870, baseEnd_377870] using wordTrace_append hprefix tailTrace_377870
  have hstable : (prefixWord ++ tailWord_377870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377870).length < 2 ^ (prefixWord ++ tailWord_377870).sum := by decide
  have hdescent : baseEnd_377870 < baseStart_377870 := by decide
  rcases family_descends (prefixWord ++ tailWord_377870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377891 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 4]
def baseStart_377891 : Nat := 118140960795 + 377891 * 2 ^ 59
def prefixEnd_377891 : Nat := 4983230072969 + 3 ^ 40 * 377891 * 2
def baseEnd_377891 : Nat := 172479749340698874155215

theorem tailTrace_377891 : CollatzResearch.WordTrace tailWord_377891 prefixEnd_377891 172479749340698874155215 := by
  unfold tailWord_377891
  simp only [CollatzResearch.WordTrace]
  refine ⟨13782817073972920489725527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9188544715981946993150351 13782817073972920489725527)
  ·
    refine ⟨20674225610959380734588291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13782817073972920489725527 20674225610959380734588291)
    ·
      refine ⟨31011338416439071101882437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20674225610959380734588291 31011338416439071101882437)
      ·
        refine ⟨5814625953082325831602957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31011338416439071101882437 5814625953082325831602957)
        ·
          refine ⟨2180484732405872186851109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5814625953082325831602957 2180484732405872186851109)
          ·
            refine ⟨408840887326101035034583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2180484732405872186851109 408840887326101035034583)
            ·
              refine ⟨613261330989151552551875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408840887326101035034583 613261330989151552551875)
              ·
                refine ⟨919891996483727328827813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613261330989151552551875 919891996483727328827813)
                ·
                  refine ⟨172479749340698874155215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 919891996483727328827813 172479749340698874155215)
                  ·
                    rfl

theorem cell20_377891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 4].length) (baseStart_377891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377891 prefixEnd_377891 := by exact prefixLift 377891
  have htrace : WordTrace (prefixWord ++ tailWord_377891) baseStart_377891 baseEnd_377891 := by
    simpa [prefixWord, tailWord_377891, baseEnd_377891] using wordTrace_append hprefix tailTrace_377891
  have hstable : (prefixWord ++ tailWord_377891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377891).length < 2 ^ (prefixWord ++ tailWord_377891).sum := by decide
  have hdescent : baseEnd_377891 < baseStart_377891 := by decide
  rcases family_descends (prefixWord ++ tailWord_377891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377905 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 3]
def baseStart_377905 : Nat := 118140960795 + 377905 * 2 ^ 59
def prefixEnd_377905 : Nat := 4983230072969 + 3 ^ 40 * 377905 * 2
def baseEnd_377905 : Nat := 172486139322177047688491

theorem tailTrace_377905 : CollatzResearch.WordTrace tailWord_377905 prefixEnd_377905 172486139322177047688491 := by
  unfold tailWord_377905
  simp only [CollatzResearch.WordTrace]
  refine ⟨13783327695922200880735169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9188885130614800587156779 13783327695922200880735169)
  ·
    refine ⟨10337495771941650660551377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13783327695922200880735169 10337495771941650660551377)
    ·
      refine ⟨7753121828956237995413533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10337495771941650660551377 7753121828956237995413533)
      ·
        refine ⟨2907420685858589248280075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7753121828956237995413533 2907420685858589248280075)
        ·
          refine ⟨4361131028787883872420113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907420685858589248280075 4361131028787883872420113)
          ·
            refine ⟨3270848271590912904315085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4361131028787883872420113 3270848271590912904315085)
            ·
              refine ⟨1226568101846592339118157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3270848271590912904315085 1226568101846592339118157)
              ·
                refine ⟨459963038192472127169309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1226568101846592339118157 459963038192472127169309)
                ·
                  refine ⟨172486139322177047688491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459963038192472127169309 172486139322177047688491)
                  ·
                    rfl

theorem cell20_377905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_377905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377905 prefixEnd_377905 := by exact prefixLift 377905
  have htrace : WordTrace (prefixWord ++ tailWord_377905) baseStart_377905 baseEnd_377905 := by
    simpa [prefixWord, tailWord_377905, baseEnd_377905] using wordTrace_append hprefix tailTrace_377905
  have hstable : (prefixWord ++ tailWord_377905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377905).length < 2 ^ (prefixWord ++ tailWord_377905).sum := by decide
  have hdescent : baseEnd_377905 < baseStart_377905 := by decide
  rcases family_descends (prefixWord ++ tailWord_377905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377942 : List Nat := [5, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_377942 : Nat := 118140960795 + 377942 * 2 ^ 59
def prefixEnd_377942 : Nat := 4983230072969 + 3 ^ 40 * 377942 * 2
def baseEnd_377942 : Nat := 172503027130369363455007

theorem tailTrace_377942 : CollatzResearch.WordTrace tailWord_377942 prefixEnd_377942 172503027130369363455007 := by
  unfold tailWord_377942
  simp only [CollatzResearch.WordTrace]
  refine ⟨861542324799259762489505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9189784797858770799888053 861542324799259762489505)
  ·
    refine ⟨646156743599444821867129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 861542324799259762489505 646156743599444821867129)
    ·
      refine ⟨484617557699583616400347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 646156743599444821867129 484617557699583616400347)
      ·
        refine ⟨726926336549375424600521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484617557699583616400347 726926336549375424600521)
        ·
          refine ⟨545194752412031568450391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726926336549375424600521 545194752412031568450391)
          ·
            refine ⟨817792128618047352675587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545194752412031568450391 817792128618047352675587)
            ·
              refine ⟨1226688192927071029013381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817792128618047352675587 1226688192927071029013381)
              ·
                refine ⟨230004036173825817940009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1226688192927071029013381 230004036173825817940009)
                ·
                  refine ⟨172503027130369363455007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230004036173825817940009 172503027130369363455007)
                  ·
                    rfl

theorem cell20_377942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_377942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377942 prefixEnd_377942 := by exact prefixLift 377942
  have htrace : WordTrace (prefixWord ++ tailWord_377942) baseStart_377942 baseEnd_377942 := by
    simpa [prefixWord, tailWord_377942, baseEnd_377942] using wordTrace_append hprefix tailTrace_377942
  have hstable : (prefixWord ++ tailWord_377942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377942).length < 2 ^ (prefixWord ++ tailWord_377942).sum := by decide
  have hdescent : baseEnd_377942 < baseStart_377942 := by decide
  rcases family_descends (prefixWord ++ tailWord_377942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377998 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_377998 : Nat := 118140960795 + 377998 * 2 ^ 59
def prefixEnd_377998 : Nat := 4983230072969 + 3 ^ 40 * 377998 * 2
def baseEnd_377998 : Nat := 172528587056282057588111

theorem tailTrace_377998 : CollatzResearch.WordTrace tailWord_377998 prefixEnd_377998 172528587056282057588111 := by
  unfold tailWord_377998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723339960573159720483831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9191146456390185175913765 1723339960573159720483831)
  ·
    refine ⟨2585009940859739580725747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1723339960573159720483831 2585009940859739580725747)
    ·
      refine ⟨3877514911289609371088621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2585009940859739580725747 3877514911289609371088621)
      ·
        refine ⟨1454068091733603514158233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3877514911289609371088621 1454068091733603514158233)
        ·
          refine ⟨1090551068800202635618675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1454068091733603514158233 1090551068800202635618675)
          ·
            refine ⟨1635826603200303953428013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090551068800202635618675 1635826603200303953428013)
            ·
              refine ⟨613434976200113982535505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1635826603200303953428013 613434976200113982535505)
              ·
                refine ⟨460076232150085486901629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613434976200113982535505 460076232150085486901629)
                ·
                  refine ⟨172528587056282057588111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460076232150085486901629 172528587056282057588111)
                  ·
                    rfl

theorem cell20_377998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_377998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377998 prefixEnd_377998 := by exact prefixLift 377998
  have htrace : WordTrace (prefixWord ++ tailWord_377998) baseStart_377998 baseEnd_377998 := by
    simpa [prefixWord, tailWord_377998, baseEnd_377998] using wordTrace_append hprefix tailTrace_377998
  have hstable : (prefixWord ++ tailWord_377998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377998).length < 2 ^ (prefixWord ++ tailWord_377998).sum := by decide
  have hdescent : baseEnd_377998 < baseStart_377998 := by decide
  rcases family_descends (prefixWord ++ tailWord_377998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378015 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 3]
def baseStart_378015 : Nat := 118140960795 + 378015 * 2 ^ 59
def prefixEnd_378015 : Nat := 4983230072969 + 3 ^ 40 * 378015 * 2
def baseEnd_378015 : Nat := 172536346319505554021375

theorem tailTrace_378015 : CollatzResearch.WordTrace tailWord_378015 prefixEnd_378015 172536346319505554021375 := by
  unfold tailWord_378015
  simp only [CollatzResearch.WordTrace]
  refine ⟨13787339725523689667239499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9191559817015793111492999 13787339725523689667239499)
  ·
    refine ⟨20681009588285534500859249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13787339725523689667239499 20681009588285534500859249)
    ·
      refine ⟨15510757191214150875644437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20681009588285534500859249 15510757191214150875644437)
      ·
        refine ⟨727066743338163322295833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15510757191214150875644437 727066743338163322295833)
        ·
          refine ⟨545300057503622491721875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727066743338163322295833 545300057503622491721875)
          ·
            refine ⟨817950086255433737582813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545300057503622491721875 817950086255433737582813)
            ·
              refine ⟨306731282345787651593555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 817950086255433737582813 306731282345787651593555)
              ·
                refine ⟨460096923518681477390333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306731282345787651593555 460096923518681477390333)
                ·
                  refine ⟨172536346319505554021375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460096923518681477390333 172536346319505554021375)
                  ·
                    rfl

theorem cell20_378015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 3].length) (baseStart_378015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378015 prefixEnd_378015 := by exact prefixLift 378015
  have htrace : WordTrace (prefixWord ++ tailWord_378015) baseStart_378015 baseEnd_378015 := by
    simpa [prefixWord, tailWord_378015, baseEnd_378015] using wordTrace_append hprefix tailTrace_378015
  have hstable : (prefixWord ++ tailWord_378015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378015).length < 2 ^ (prefixWord ++ tailWord_378015).sum := by decide
  have hdescent : baseEnd_378015 < baseStart_378015 := by decide
  rcases family_descends (prefixWord ++ tailWord_378015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378047 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_378047 : Nat := 118140960795 + 378047 * 2 ^ 59
def prefixEnd_378047 : Nat := 4983230072969 + 3 ^ 40 * 378047 * 2
def baseEnd_378047 : Nat := 172550951991455664954577

theorem tailTrace_378047 : CollatzResearch.WordTrace tailWord_378047 prefixEnd_378047 172550951991455664954577 := by
  unfold tailWord_378047
  simp only [CollatzResearch.WordTrace]
  refine ⟨13788506861407759132404395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9192337907605172754936263 13788506861407759132404395)
  ·
    refine ⟨20682760292111638698606593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13788506861407759132404395 20682760292111638698606593)
    ·
      refine ⟨15512070219083729023954945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20682760292111638698606593 15512070219083729023954945)
      ·
        refine ⟨11634052664312796767966209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15512070219083729023954945 11634052664312796767966209)
        ·
          refine ⟨8725539498234597575974657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11634052664312796767966209 8725539498234597575974657)
          ·
            refine ⟨6544154623675948181980993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8725539498234597575974657 6544154623675948181980993)
            ·
              refine ⟨4908115967756961136485745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6544154623675948181980993 4908115967756961136485745)
              ·
                refine ⟨3681086975817720852364309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4908115967756961136485745 3681086975817720852364309)
                ·
                  refine ⟨172550951991455664954577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3681086975817720852364309 172550951991455664954577)
                  ·
                    rfl

theorem cell20_378047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_378047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378047 prefixEnd_378047 := by exact prefixLift 378047
  have htrace : WordTrace (prefixWord ++ tailWord_378047) baseStart_378047 baseEnd_378047 := by
    simpa [prefixWord, tailWord_378047, baseEnd_378047] using wordTrace_append hprefix tailTrace_378047
  have hstable : (prefixWord ++ tailWord_378047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378047).length < 2 ^ (prefixWord ++ tailWord_378047).sum := by decide
  have hdescent : baseEnd_378047 < baseStart_378047 := by decide
  rcases family_descends (prefixWord ++ tailWord_378047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378126 : List Nat := [4, 1, 1, 2, 1, 5, 1, 5]
def baseStart_378126 : Nat := 118140960795 + 378126 * 2 ^ 59
def prefixEnd_378126 : Nat := 4983230072969 + 3 ^ 40 * 378126 * 2
def baseEnd_378126 : Nat := 57529003248027500440307

theorem tailTrace_378126 : CollatzResearch.WordTrace tailWord_378126 prefixEnd_378126 57529003248027500440307 := by
  unfold tailWord_378126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723923528515194453066279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9194258818747703749686821 1723923528515194453066279)
  ·
    refine ⟨2585885292772791679599419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1723923528515194453066279 2585885292772791679599419)
    ·
      refine ⟨3878827939159187519399129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2585885292772791679599419 3878827939159187519399129)
      ·
        refine ⟨2909120954369390639549347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3878827939159187519399129 2909120954369390639549347)
        ·
          refine ⟨4363681431554085959324021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909120954369390639549347 4363681431554085959324021)
          ·
            refine ⟨409095134208195558686627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4363681431554085959324021 409095134208195558686627)
            ·
              refine ⟨613642701312293338029941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409095134208195558686627 613642701312293338029941)
              ·
                refine ⟨57529003248027500440307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 613642701312293338029941 57529003248027500440307)
                ·
                  rfl

theorem cell20_378126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_378126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378126 prefixEnd_378126 := by exact prefixLift 378126
  have htrace : WordTrace (prefixWord ++ tailWord_378126) baseStart_378126 baseEnd_378126 := by
    simpa [prefixWord, tailWord_378126, baseEnd_378126] using wordTrace_append hprefix tailTrace_378126
  have hstable : (prefixWord ++ tailWord_378126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378126).length < 2 ^ (prefixWord ++ tailWord_378126).sum := by decide
  have hdescent : baseEnd_378126 < baseStart_378126 := by decide
  rcases family_descends (prefixWord ++ tailWord_378126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378188 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 3]
def baseStart_378188 : Nat := 118140960795 + 378188 * 2 ^ 59
def prefixEnd_378188 : Nat := 4983230072969 + 3 ^ 40 * 378188 * 2
def baseEnd_378188 : Nat := 172615308233485841254001

theorem tailTrace_378188 : CollatzResearch.WordTrace tailWord_378188 prefixEnd_378188 172615308233485841254001 := by
  unfold tailWord_378188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6896824776948470106643609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9195766369264626808858145 6896824776948470106643609)
  ·
    refine ⟨5172618582711352579982707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6896824776948470106643609 5172618582711352579982707)
    ·
      refine ⟨7758927874067028869974061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5172618582711352579982707 7758927874067028869974061)
      ·
        refine ⟨2909597952775135826240273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7758927874067028869974061 2909597952775135826240273)
        ·
          refine ⟨2182198464581351869680205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2909597952775135826240273 2182198464581351869680205)
          ·
            refine ⟨818324424218006951130077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2182198464581351869680205 818324424218006951130077)
            ·
              refine ⟨306871659081752606673779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818324424218006951130077 306871659081752606673779)
              ·
                refine ⟨460307488622628910010669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306871659081752606673779 460307488622628910010669)
                ·
                  refine ⟨172615308233485841254001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460307488622628910010669 172615308233485841254001)
                  ·
                    rfl

theorem cell20_378188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_378188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378188 prefixEnd_378188 := by exact prefixLift 378188
  have htrace : WordTrace (prefixWord ++ tailWord_378188) baseStart_378188 baseEnd_378188 := by
    simpa [prefixWord, tailWord_378188, baseEnd_378188] using wordTrace_append hprefix tailTrace_378188
  have hstable : (prefixWord ++ tailWord_378188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378188).length < 2 ^ (prefixWord ++ tailWord_378188).sum := by decide
  have hdescent : baseEnd_378188 < baseStart_378188 := by decide
  rcases family_descends (prefixWord ++ tailWord_378188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378212 : List Nat := [2, 3, 1, 1, 3, 4, 1, 3, 2]
def baseStart_378212 : Nat := 118140960795 + 378212 * 2 ^ 59
def prefixEnd_378212 : Nat := 4983230072969 + 3 ^ 40 * 378212 * 2
def baseEnd_378212 : Nat := 172626262487448424453903

theorem tailTrace_378212 : CollatzResearch.WordTrace tailWord_378212 prefixEnd_378212 172626262487448424453903 := by
  unfold tailWord_378212
  simp only [CollatzResearch.WordTrace]
  refine ⟨6897262452904996156080445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9196349937206661541440593 6897262452904996156080445)
  ·
    refine ⟨2586473419839373558530167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6897262452904996156080445 2586473419839373558530167)
    ·
      refine ⟨3879710129759060337795251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2586473419839373558530167 3879710129759060337795251)
      ·
        refine ⟨5819565194638590506692877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3879710129759060337795251 5819565194638590506692877)
        ·
          refine ⟨2182336947989471440009829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5819565194638590506692877 2182336947989471440009829)
          ·
            refine ⟨409188177748025895001843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2182336947989471440009829 409188177748025895001843)
            ·
              refine ⟨613782266622038842502765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409188177748025895001843 613782266622038842502765)
              ·
                refine ⟨230168349983264565938537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 613782266622038842502765 230168349983264565938537)
                ·
                  refine ⟨172626262487448424453903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230168349983264565938537 172626262487448424453903)
                  ·
                    rfl

theorem cell20_378212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_378212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378212 prefixEnd_378212 := by exact prefixLift 378212
  have htrace : WordTrace (prefixWord ++ tailWord_378212) baseStart_378212 baseEnd_378212 := by
    simpa [prefixWord, tailWord_378212, baseEnd_378212] using wordTrace_append hprefix tailTrace_378212
  have hstable : (prefixWord ++ tailWord_378212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378212).length < 2 ^ (prefixWord ++ tailWord_378212).sum := by decide
  have hdescent : baseEnd_378212 < baseStart_378212 := by decide
  rcases family_descends (prefixWord ++ tailWord_378212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378229 : List Nat := [1, 3, 4, 1, 3, 1, 3, 2, 2]
def baseStart_378229 : Nat := 118140960795 + 378229 * 2 ^ 59
def prefixEnd_378229 : Nat := 4983230072969 + 3 ^ 40 * 378229 * 2
def baseEnd_378229 : Nat := 172634021750671920887167

theorem tailTrace_378229 : CollatzResearch.WordTrace tailWord_378229 prefixEnd_378229 172634021750671920887167 := by
  unfold tailWord_378229
  simp only [CollatzResearch.WordTrace]
  refine ⟨13795144946748404215529741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9196763297832269477019827 13795144946748404215529741)
  ·
    refine ⟨5173179355030651580823653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13795144946748404215529741 5173179355030651580823653)
    ·
      refine ⟨969971129068247171404435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5173179355030651580823653 969971129068247171404435)
      ·
        refine ⟨1454956693602370757106653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969971129068247171404435 1454956693602370757106653)
        ·
          refine ⟨545608760100889033914995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1454956693602370757106653 545608760100889033914995)
          ·
            refine ⟨818413140151333550872493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545608760100889033914995 818413140151333550872493)
            ·
              refine ⟨306904927556750081577185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818413140151333550872493 306904927556750081577185)
              ·
                refine ⟨230178695667562561182889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306904927556750081577185 230178695667562561182889)
                ·
                  refine ⟨172634021750671920887167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230178695667562561182889 172634021750671920887167)
                  ·
                    rfl

theorem cell20_378229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_378229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378229 prefixEnd_378229 := by exact prefixLift 378229
  have htrace : WordTrace (prefixWord ++ tailWord_378229) baseStart_378229 baseEnd_378229 := by
    simpa [prefixWord, tailWord_378229, baseEnd_378229] using wordTrace_append hprefix tailTrace_378229
  have hstable : (prefixWord ++ tailWord_378229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378229).length < 2 ^ (prefixWord ++ tailWord_378229).sum := by decide
  have hdescent : baseEnd_378229 < baseStart_378229 := by decide
  rcases family_descends (prefixWord ++ tailWord_378229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378247 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 3]
def baseStart_378247 : Nat := 118140960795 + 378247 * 2 ^ 59
def prefixEnd_378247 : Nat := 4983230072969 + 3 ^ 40 * 378247 * 2
def baseEnd_378247 : Nat := 172642237441143858287093

theorem tailTrace_378247 : CollatzResearch.WordTrace tailWord_378247 prefixEnd_378247 172642237441143858287093 := by
  unfold tailWord_378247
  simp only [CollatzResearch.WordTrace]
  refine ⟨13795801460683193289684995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9197200973788795526456663 13795801460683193289684995)
  ·
    refine ⟨20693702191024789934527493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13795801460683193289684995 20693702191024789934527493)
    ·
      refine ⟨3880069160817148112723905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20693702191024789934527493 3880069160817148112723905)
      ·
        refine ⟨2910051870612861084542929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3880069160817148112723905 2910051870612861084542929)
        ·
          refine ⟨2182538902959645813407197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2910051870612861084542929 2182538902959645813407197)
          ·
            refine ⟨818452088609867180027699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2182538902959645813407197 818452088609867180027699)
            ·
              refine ⟨1227678132914800770041549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818452088609867180027699 1227678132914800770041549)
              ·
                refine ⟨460379299843050288765581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1227678132914800770041549 460379299843050288765581)
                ·
                  refine ⟨172642237441143858287093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460379299843050288765581 172642237441143858287093)
                  ·
                    rfl

theorem cell20_378247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 3].length) (baseStart_378247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378247 prefixEnd_378247 := by exact prefixLift 378247
  have htrace : WordTrace (prefixWord ++ tailWord_378247) baseStart_378247 baseEnd_378247 := by
    simpa [prefixWord, tailWord_378247, baseEnd_378247] using wordTrace_append hprefix tailTrace_378247
  have hstable : (prefixWord ++ tailWord_378247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378247).length < 2 ^ (prefixWord ++ tailWord_378247).sum := by decide
  have hdescent : baseEnd_378247 < baseStart_378247 := by decide
  rcases family_descends (prefixWord ++ tailWord_378247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378316 : List Nat := [2, 2, 1, 4, 2, 2, 3, 4]
def baseStart_378316 : Nat := 118140960795 + 378316 * 2 ^ 59
def prefixEnd_378316 : Nat := 4983230072969 + 3 ^ 40 * 378316 * 2
def baseEnd_378316 : Nat := 57557910307095428328937

theorem tailTrace_378316 : CollatzResearch.WordTrace tailWord_378316 prefixEnd_378316 57557910307095428328937 := by
  unfold tailWord_378316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899159048716609036973401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9198878731622145382631201 6899159048716609036973401)
  ·
    refine ⟨5174369286537456777730051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6899159048716609036973401 5174369286537456777730051)
    ·
      refine ⟨7761553929806185166595077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5174369286537456777730051 7761553929806185166595077)
      ·
        refine ⟨1455291361838659718736577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7761553929806185166595077 1455291361838659718736577)
        ·
          refine ⟨1091468521378994789052433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455291361838659718736577 1091468521378994789052433)
          ·
            refine ⟨818601391034246091789325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091468521378994789052433 818601391034246091789325)
            ·
              refine ⟨306975521637842284420997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818601391034246091789325 306975521637842284420997)
              ·
                refine ⟨57557910307095428328937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306975521637842284420997 57557910307095428328937)
                ·
                  rfl

theorem cell20_378316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_378316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378316 prefixEnd_378316 := by exact prefixLift 378316
  have htrace : WordTrace (prefixWord ++ tailWord_378316) baseStart_378316 baseEnd_378316 := by
    simpa [prefixWord, tailWord_378316, baseEnd_378316] using wordTrace_append hprefix tailTrace_378316
  have hstable : (prefixWord ++ tailWord_378316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378316).length < 2 ^ (prefixWord ++ tailWord_378316).sum := by decide
  have hdescent : baseEnd_378316 < baseStart_378316 := by decide
  rcases family_descends (prefixWord ++ tailWord_378316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378326 : List Nat := [5, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_378326 : Nat := 118140960795 + 378326 * 2 ^ 59
def prefixEnd_378326 : Nat := 4983230072969 + 3 ^ 40 * 378326 * 2
def baseEnd_378326 : Nat := 172678295193770694653437

theorem tailTrace_378326 : CollatzResearch.WordTrace tailWord_378326 prefixEnd_378326 172678295193770694653437 := by
  unfold tailWord_378326
  simp only [CollatzResearch.WordTrace]
  refine ⟨862417676712311861363177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9199121884931326521207221 862417676712311861363177)
  ·
    refine ⟨646813257534233896022383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 862417676712311861363177 646813257534233896022383)
    ·
      refine ⟨970219886301350844033575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646813257534233896022383 970219886301350844033575)
      ·
        refine ⟨1455329829452026266050363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970219886301350844033575 1455329829452026266050363)
        ·
          refine ⟨2182994744178039399075545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455329829452026266050363 2182994744178039399075545)
          ·
            refine ⟨1637246058133529549306659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2182994744178039399075545 1637246058133529549306659)
            ·
              refine ⟨2455869087200294323959989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637246058133529549306659 2455869087200294323959989)
              ·
                refine ⟨230237726925027592871249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2455869087200294323959989 230237726925027592871249)
                ·
                  refine ⟨172678295193770694653437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230237726925027592871249 172678295193770694653437)
                  ·
                    rfl

theorem cell20_378326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_378326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378326 prefixEnd_378326 := by exact prefixLift 378326
  have htrace : WordTrace (prefixWord ++ tailWord_378326) baseStart_378326 baseEnd_378326 := by
    simpa [prefixWord, tailWord_378326, baseEnd_378326] using wordTrace_append hprefix tailTrace_378326
  have hstable : (prefixWord ++ tailWord_378326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378326).length < 2 ^ (prefixWord ++ tailWord_378326).sum := by decide
  have hdescent : baseEnd_378326 < baseStart_378326 := by decide
  rcases family_descends (prefixWord ++ tailWord_378326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378344 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_378344 : Nat := 118140960795 + 378344 * 2 ^ 59
def prefixEnd_378344 : Nat := 4983230072969 + 3 ^ 40 * 378344 * 2
def baseEnd_378344 : Nat := 172686510884242632053363

theorem tailTrace_378344 : CollatzResearch.WordTrace tailWord_378344 prefixEnd_378344 172686510884242632053363 := by
  unfold tailWord_378344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899669670665889427983043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9199559560887852570644057 6899669670665889427983043)
  ·
    refine ⟨10349504505998834141974565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6899669670665889427983043 10349504505998834141974565)
    ·
      refine ⟨1940532094874781401620231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10349504505998834141974565 1940532094874781401620231)
      ·
        refine ⟨2910798142312172102430347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1940532094874781401620231 2910798142312172102430347)
        ·
          refine ⟨4366197213468258153645521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2910798142312172102430347 4366197213468258153645521)
          ·
            refine ⟨3274647910101193615234141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4366197213468258153645521 3274647910101193615234141)
            ·
              refine ⟨1227992966287947605712803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3274647910101193615234141 1227992966287947605712803)
              ·
                refine ⟨1841989449431921408569205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227992966287947605712803 1841989449431921408569205)
                ·
                  refine ⟨172686510884242632053363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1841989449431921408569205 172686510884242632053363)
                  ·
                    rfl

theorem cell20_378344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_378344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378344 prefixEnd_378344 := by exact prefixLift 378344
  have htrace : WordTrace (prefixWord ++ tailWord_378344) baseStart_378344 baseEnd_378344 := by
    simpa [prefixWord, tailWord_378344, baseEnd_378344] using wordTrace_append hprefix tailTrace_378344
  have hstable : (prefixWord ++ tailWord_378344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378344).length < 2 ^ (prefixWord ++ tailWord_378344).sum := by decide
  have hdescent : baseEnd_378344 < baseStart_378344 := by decide
  rcases family_descends (prefixWord ++ tailWord_378344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378351 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_378351 : Nat := 118140960795 + 378351 * 2 ^ 59
def prefixEnd_378351 : Nat := 4983230072969 + 3 ^ 40 * 378351 * 2
def baseEnd_378351 : Nat := 172689705874981718820001

theorem tailTrace_378351 : CollatzResearch.WordTrace tailWord_378351 prefixEnd_378351 172689705874981718820001 := by
  unfold tailWord_378351
  simp only [CollatzResearch.WordTrace]
  refine ⟨13799594652306419051470907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9199729768204279367647271 13799594652306419051470907)
  ·
    refine ⟨20699391978459628577206361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13799594652306419051470907 20699391978459628577206361)
    ·
      refine ⟨15524543983844721432904771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20699391978459628577206361 15524543983844721432904771)
      ·
        refine ⟨23286815975767082149357157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15524543983844721432904771 23286815975767082149357157)
        ·
          refine ⟨4366277995456327903004467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23286815975767082149357157 4366277995456327903004467)
          ·
            refine ⟨6549416993184491854506701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366277995456327903004467 6549416993184491854506701)
            ·
              refine ⟨2456031372444184445440013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6549416993184491854506701 2456031372444184445440013)
              ·
                refine ⟨921011764666569167040005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2456031372444184445440013 921011764666569167040005)
                ·
                  refine ⟨172689705874981718820001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921011764666569167040005 172689705874981718820001)
                  ·
                    rfl

theorem cell20_378351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_378351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378351 prefixEnd_378351 := by exact prefixLift 378351
  have htrace : WordTrace (prefixWord ++ tailWord_378351) baseStart_378351 baseEnd_378351 := by
    simpa [prefixWord, tailWord_378351, baseEnd_378351] using wordTrace_append hprefix tailTrace_378351
  have hstable : (prefixWord ++ tailWord_378351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378351).length < 2 ^ (prefixWord ++ tailWord_378351).sum := by decide
  have hdescent : baseEnd_378351 < baseStart_378351 := by decide
  rcases family_descends (prefixWord ++ tailWord_378351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378357 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 3]
def baseStart_378357 : Nat := 118140960795 + 378357 * 2 ^ 59
def prefixEnd_378357 : Nat := 4983230072969 + 3 ^ 40 * 378357 * 2
def baseEnd_378357 : Nat := 172692444438472364619977

theorem tailTrace_378357 : CollatzResearch.WordTrace tailWord_378357 prefixEnd_378357 172692444438472364619977 := by
  unfold tailWord_378357
  simp only [CollatzResearch.WordTrace]
  refine ⟨13799813490284682076189325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9199875660189788050792883 13799813490284682076189325)
  ·
    refine ⟨5174930058856755778570997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13799813490284682076189325 5174930058856755778570997)
    ·
      refine ⟨485149693017820854241031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5174930058856755778570997 485149693017820854241031)
      ·
        refine ⟨727724539526731281361547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485149693017820854241031 727724539526731281361547)
        ·
          refine ⟨1091586809290096922042321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727724539526731281361547 1091586809290096922042321)
          ·
            refine ⟨818690106967572691531741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091586809290096922042321 818690106967572691531741)
            ·
              refine ⟨307008790112839759324403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818690106967572691531741 307008790112839759324403)
              ·
                refine ⟨460513185169259638986605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307008790112839759324403 460513185169259638986605)
                ·
                  refine ⟨172692444438472364619977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460513185169259638986605 172692444438472364619977)
                  ·
                    rfl

theorem cell20_378357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_378357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378357 prefixEnd_378357 := by exact prefixLift 378357
  have htrace : WordTrace (prefixWord ++ tailWord_378357) baseStart_378357 baseEnd_378357 := by
    simpa [prefixWord, tailWord_378357, baseEnd_378357] using wordTrace_append hprefix tailTrace_378357
  have hstable : (prefixWord ++ tailWord_378357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378357).length < 2 ^ (prefixWord ++ tailWord_378357).sum := by decide
  have hdescent : baseEnd_378357 < baseStart_378357 := by decide
  rcases family_descends (prefixWord ++ tailWord_378357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378375 : List Nat := [1, 1, 4, 3, 2, 2, 1, 6]
def baseStart_378375 : Nat := 118140960795 + 378375 * 2 ^ 59
def prefixEnd_378375 : Nat := 4983230072969 + 3 ^ 40 * 378375 * 2
def baseEnd_378375 : Nat := 57566886709648100673301

theorem tailTrace_378375 : CollatzResearch.WordTrace tailWord_378375 prefixEnd_378375 57566886709648100673301 := by
  unfold tailWord_378375
  simp only [CollatzResearch.WordTrace]
  refine ⟨13800470004219471150344579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9200313336146314100229719 13800470004219471150344579)
  ·
    refine ⟨20700705006329206725516869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13800470004219471150344579 20700705006329206725516869)
    ·
      refine ⟨3881382188686726261034413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20700705006329206725516869 3881382188686726261034413)
      ·
        refine ⟨1455518320757522347887905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3881382188686726261034413 1455518320757522347887905)
        ·
          refine ⟨1091638740568141760915929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455518320757522347887905 1091638740568141760915929)
          ·
            refine ⟨818729055426106320686947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091638740568141760915929 818729055426106320686947)
            ·
              refine ⟨1228093583139159481030421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818729055426106320686947 1228093583139159481030421)
              ·
                refine ⟨57566886709648100673301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1228093583139159481030421 57566886709648100673301)
                ·
                  rfl

theorem cell20_378375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_378375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378375 prefixEnd_378375 := by exact prefixLift 378375
  have htrace : WordTrace (prefixWord ++ tailWord_378375) baseStart_378375 baseEnd_378375 := by
    simpa [prefixWord, tailWord_378375, baseEnd_378375] using wordTrace_append hprefix tailTrace_378375
  have hstable : (prefixWord ++ tailWord_378375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378375).length < 2 ^ (prefixWord ++ tailWord_378375).sum := by decide
  have hdescent : baseEnd_378375 < baseStart_378375 := by decide
  rcases family_descends (prefixWord ++ tailWord_378375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378392 : List Nat := [2, 1, 2, 3, 5, 1, 6]
def baseStart_378392 : Nat := 118140960795 + 378392 * 2 ^ 59
def prefixEnd_378392 : Nat := 4983230072969 + 3 ^ 40 * 378392 * 2
def baseEnd_378392 : Nat := 19189824376907533161463

theorem tailTrace_378392 : CollatzResearch.WordTrace tailWord_378392 prefixEnd_378392 19189824376907533161463 := by
  unfold tailWord_378392
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900545022578941526856715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9200726696771922035808953 6900545022578941526856715)
  ·
    refine ⟨10350817533868412290285073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6900545022578941526856715 10350817533868412290285073)
    ·
      refine ⟨7763113150401309217713805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10350817533868412290285073 7763113150401309217713805)
      ·
        refine ⟨2911167431400490956642677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7763113150401309217713805 2911167431400490956642677)
        ·
          refine ⟨272921946693796027185251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2911167431400490956642677 272921946693796027185251)
          ·
            refine ⟨409382920040694040777877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272921946693796027185251 409382920040694040777877)
            ·
              refine ⟨19189824376907533161463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 409382920040694040777877 19189824376907533161463)
              ·
                rfl

theorem cell20_378392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 6].length) (baseStart_378392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378392 prefixEnd_378392 := by exact prefixLift 378392
  have htrace : WordTrace (prefixWord ++ tailWord_378392) baseStart_378392 baseEnd_378392 := by
    simpa [prefixWord, tailWord_378392, baseEnd_378392] using wordTrace_append hprefix tailTrace_378392
  have hstable : (prefixWord ++ tailWord_378392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378392).length < 2 ^ (prefixWord ++ tailWord_378392).sum := by decide
  have hdescent : baseEnd_378392 < baseStart_378392 := by decide
  rcases family_descends (prefixWord ++ tailWord_378392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378398 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_378398 : Nat := 118140960795 + 378398 * 2 ^ 59
def prefixEnd_378398 : Nat := 4983230072969 + 3 ^ 40 * 378398 * 2
def baseEnd_378398 : Nat := 172711157955658444253143

theorem tailTrace_378398 : CollatzResearch.WordTrace tailWord_378398 prefixEnd_378398 172711157955658444253143 := by
  unfold tailWord_378398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1725163610392018259803981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9200872588757430718954565 1725163610392018259803981)
  ·
    refine ⟨646936353897006847426493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1725163610392018259803981 646936353897006847426493)
    ·
      refine ⟨242601132711377567784935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 646936353897006847426493 242601132711377567784935)
      ·
        refine ⟨363901699067066351677403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242601132711377567784935 363901699067066351677403)
        ·
          refine ⟨545852548600599527516105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363901699067066351677403 545852548600599527516105)
          ·
            refine ⟨409389411450449645637079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545852548600599527516105 409389411450449645637079)
            ·
              refine ⟨614084117175674468455619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409389411450449645637079 614084117175674468455619)
              ·
                refine ⟨921126175763511702683429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614084117175674468455619 921126175763511702683429)
                ·
                  refine ⟨172711157955658444253143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921126175763511702683429 172711157955658444253143)
                  ·
                    rfl

theorem cell20_378398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_378398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378398 prefixEnd_378398 := by exact prefixLift 378398
  have htrace : WordTrace (prefixWord ++ tailWord_378398) baseStart_378398 baseEnd_378398 := by
    simpa [prefixWord, tailWord_378398, baseEnd_378398] using wordTrace_append hprefix tailTrace_378398
  have hstable : (prefixWord ++ tailWord_378398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378398).length < 2 ^ (prefixWord ++ tailWord_378398).sum := by decide
  have hdescent : baseEnd_378398 < baseStart_378398 := by decide
  rcases family_descends (prefixWord ++ tailWord_378398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378441 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_378441 : Nat := 118140960795 + 378441 * 2 ^ 59
def prefixEnd_378441 : Nat := 4983230072969 + 3 ^ 40 * 378441 * 2
def baseEnd_378441 : Nat := 172730784327341405819633

theorem tailTrace_378441 : CollatzResearch.WordTrace tailWord_378441 prefixEnd_378441 172730784327341405819633 := by
  unfold tailWord_378441
  simp only [CollatzResearch.WordTrace]
  refine ⟨13802877221980364422247177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9201918147986909614831451 13802877221980364422247177)
  ·
    refine ⟨10352157916485273316685383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13802877221980364422247177 10352157916485273316685383)
    ·
      refine ⟨15528236874727909975028075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10352157916485273316685383 15528236874727909975028075)
      ·
        refine ⟨23292355312091864962542113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15528236874727909975028075 23292355312091864962542113)
        ·
          refine ⟨17469266484068898721906585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23292355312091864962542113 17469266484068898721906585)
          ·
            refine ⟨13101949863051674041429939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17469266484068898721906585 13101949863051674041429939)
            ·
              refine ⟨19652924794577511062144909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13101949863051674041429939 19652924794577511062144909)
              ·
                refine ⟨7369846797966566648304341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19652924794577511062144909 7369846797966566648304341)
                ·
                  refine ⟨172730784327341405819633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7369846797966566648304341 172730784327341405819633)
                  ·
                    rfl

theorem cell20_378441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_378441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378441 prefixEnd_378441 := by exact prefixLift 378441
  have htrace : WordTrace (prefixWord ++ tailWord_378441) baseStart_378441 baseEnd_378441 := by
    simpa [prefixWord, tailWord_378441, baseEnd_378441] using wordTrace_append hprefix tailTrace_378441
  have hstable : (prefixWord ++ tailWord_378441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378441).length < 2 ^ (prefixWord ++ tailWord_378441).sum := by decide
  have hdescent : baseEnd_378441 < baseStart_378441 := by decide
  rcases family_descends (prefixWord ++ tailWord_378441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378465 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_378465 : Nat := 118140960795 + 378465 * 2 ^ 59
def prefixEnd_378465 : Nat := 4983230072969 + 3 ^ 40 * 378465 * 2
def baseEnd_378465 : Nat := 172741738581303989019535

theorem tailTrace_378465 : CollatzResearch.WordTrace tailWord_378465 prefixEnd_378465 172741738581303989019535 := by
  unfold tailWord_378465
  simp only [CollatzResearch.WordTrace]
  refine ⟨13803752573893416521120849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9202501715928944347413899 13803752573893416521120849)
  ·
    refine ⟨10352814430420062390840637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13803752573893416521120849 10352814430420062390840637)
    ·
      refine ⟨3882305411407523396565239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10352814430420062390840637 3882305411407523396565239)
      ·
        refine ⟨5823458117111285094847859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3882305411407523396565239 5823458117111285094847859)
        ·
          refine ⟨8735187175666927642271789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5823458117111285094847859 8735187175666927642271789)
          ·
            refine ⟨3275695190875097865851921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8735187175666927642271789 3275695190875097865851921)
            ·
              refine ⟨2456771393156323399388941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3275695190875097865851921 2456771393156323399388941)
              ·
                refine ⟨921289272433621274770853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2456771393156323399388941 921289272433621274770853)
                ·
                  refine ⟨172741738581303989019535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921289272433621274770853 172741738581303989019535)
                  ·
                    rfl

theorem cell20_378465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_378465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378465 prefixEnd_378465 := by exact prefixLift 378465
  have htrace : WordTrace (prefixWord ++ tailWord_378465) baseStart_378465 baseEnd_378465 := by
    simpa [prefixWord, tailWord_378465, baseEnd_378465] using wordTrace_append hprefix tailTrace_378465
  have hstable : (prefixWord ++ tailWord_378465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378465).length < 2 ^ (prefixWord ++ tailWord_378465).sum := by decide
  have hdescent : baseEnd_378465 < baseStart_378465 := by decide
  rcases family_descends (prefixWord ++ tailWord_378465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378479 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_378479 : Nat := 118140960795 + 378479 * 2 ^ 59
def prefixEnd_378479 : Nat := 4983230072969 + 3 ^ 40 * 378479 * 2
def baseEnd_378479 : Nat := 172748128562782162552811

theorem tailTrace_378479 : CollatzResearch.WordTrace tailWord_378479 prefixEnd_378479 172748128562782162552811 := by
  unfold tailWord_378479
  simp only [CollatzResearch.WordTrace]
  refine ⟨13804263195842696912130491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9202842130561797941420327 13804263195842696912130491)
  ·
    refine ⟨20706394793764045368195737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13804263195842696912130491 20706394793764045368195737)
    ·
      refine ⟨15529796095323034026146803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20706394793764045368195737 15529796095323034026146803)
      ·
        refine ⟨23294694142984551039220205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15529796095323034026146803 23294694142984551039220205)
        ·
          refine ⟨8735510303619206639707577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23294694142984551039220205 8735510303619206639707577)
          ·
            refine ⟨6551632727714404979780683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8735510303619206639707577 6551632727714404979780683)
            ·
              refine ⟨9827449091571607469671025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6551632727714404979780683 9827449091571607469671025)
              ·
                refine ⟨7370586818678705602253269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9827449091571607469671025 7370586818678705602253269)
                ·
                  refine ⟨172748128562782162552811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7370586818678705602253269 172748128562782162552811)
                  ·
                    rfl

theorem cell20_378479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_378479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378479 prefixEnd_378479 := by exact prefixLift 378479
  have htrace : WordTrace (prefixWord ++ tailWord_378479) baseStart_378479 baseEnd_378479 := by
    simpa [prefixWord, tailWord_378479, baseEnd_378479] using wordTrace_append hprefix tailTrace_378479
  have hstable : (prefixWord ++ tailWord_378479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378479).length < 2 ^ (prefixWord ++ tailWord_378479).sum := by decide
  have hdescent : baseEnd_378479 < baseStart_378479 := by decide
  rcases family_descends (prefixWord ++ tailWord_378479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378482 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_378482 : Nat := 118140960795 + 378482 * 2 ^ 59
def prefixEnd_378482 : Nat := 4983230072969 + 3 ^ 40 * 378482 * 2
def baseEnd_378482 : Nat := 172749497844527485452799

theorem tailTrace_378482 : CollatzResearch.WordTrace tailWord_378482 prefixEnd_378482 172749497844527485452799 := by
  unfold tailWord_378482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3451093153707957106122425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9202915076554552282993133 3451093153707957106122425)
  ·
    refine ⟨2588319865280967829591819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3451093153707957106122425 2588319865280967829591819)
    ·
      refine ⟨3882479797921451744387729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2588319865280967829591819 3882479797921451744387729)
      ·
        refine ⟨2911859848441088808290797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3882479797921451744387729 2911859848441088808290797)
        ·
          refine ⟨1091947443165408303109049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2911859848441088808290797 1091947443165408303109049)
          ·
            refine ⟨818960582374056227331787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091947443165408303109049 818960582374056227331787)
            ·
              refine ⟨1228440873561084340997681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818960582374056227331787 1228440873561084340997681)
              ·
                refine ⟨921330655170813255748261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1228440873561084340997681 921330655170813255748261)
                ·
                  refine ⟨172749497844527485452799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921330655170813255748261 172749497844527485452799)
                  ·
                    rfl

theorem cell20_378482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_378482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378482 prefixEnd_378482 := by exact prefixLift 378482
  have htrace : WordTrace (prefixWord ++ tailWord_378482) baseStart_378482 baseEnd_378482 := by
    simpa [prefixWord, tailWord_378482, baseEnd_378482] using wordTrace_append hprefix tailTrace_378482
  have hstable : (prefixWord ++ tailWord_378482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378482).length < 2 ^ (prefixWord ++ tailWord_378482).sum := by decide
  have hdescent : baseEnd_378482 < baseStart_378482 := by decide
  rcases family_descends (prefixWord ++ tailWord_378482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378489 : List Nat := [1, 2, 1, 3, 3, 1, 5, 4]
def baseStart_378489 : Nat := 118140960795 + 378489 * 2 ^ 59
def prefixEnd_378489 : Nat := 4983230072969 + 3 ^ 40 * 378489 * 2
def baseEnd_378489 : Nat := 57584230945088857406479

theorem tailTrace_378489 : CollatzResearch.WordTrace tailWord_378489 prefixEnd_378489 57584230945088857406479 := by
  unfold tailWord_378489
  simp only [CollatzResearch.WordTrace]
  refine ⟨13804627925806468619994521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9203085283870979079996347 13804627925806468619994521)
  ·
    refine ⟨10353470944354851464995891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13804627925806468619994521 10353470944354851464995891)
    ·
      refine ⟨15530206416532277197493837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10353470944354851464995891 15530206416532277197493837)
      ·
        refine ⟨5823827406199603949060189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15530206416532277197493837 5823827406199603949060189)
        ·
          refine ⟨2183935277324851480897571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5823827406199603949060189 2183935277324851480897571)
          ·
            refine ⟨3275902915987277221346357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183935277324851480897571 3275902915987277221346357)
            ·
              refine ⟨307115898373807239501221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3275902915987277221346357 307115898373807239501221)
              ·
                refine ⟨57584230945088857406479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307115898373807239501221 57584230945088857406479)
                ·
                  rfl

theorem cell20_378489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 4].length) (baseStart_378489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378489 prefixEnd_378489 := by exact prefixLift 378489
  have htrace : WordTrace (prefixWord ++ tailWord_378489) baseStart_378489 baseEnd_378489 := by
    simpa [prefixWord, tailWord_378489, baseEnd_378489] using wordTrace_append hprefix tailTrace_378489
  have hstable : (prefixWord ++ tailWord_378489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378489).length < 2 ^ (prefixWord ++ tailWord_378489).sum := by decide
  have hdescent : baseEnd_378489 < baseStart_378489 := by decide
  rcases family_descends (prefixWord ++ tailWord_378489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378520 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_378520 : Nat := 118140960795 + 378520 * 2 ^ 59
def prefixEnd_378520 : Nat := 4983230072969 + 3 ^ 40 * 378520 * 2
def baseEnd_378520 : Nat := 172766842079968242185977

theorem tailTrace_378520 : CollatzResearch.WordTrace tailWord_378520 prefixEnd_378520 172766842079968242185977 := by
  unfold tailWord_378520
  simp only [CollatzResearch.WordTrace]
  refine ⟨6902879294347080457186507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9203839059129440609582009 6902879294347080457186507)
  ·
    refine ⟨10354318941520620685779761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6902879294347080457186507 10354318941520620685779761)
    ·
      refine ⟨7765739206140465514334821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10354318941520620685779761 7765739206140465514334821)
      ·
        refine ⟨1456076101151337283937779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7765739206140465514334821 1456076101151337283937779)
        ·
          refine ⟨2184114151727005925906669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456076101151337283937779 2184114151727005925906669)
          ·
            refine ⟨819042806897627222215001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2184114151727005925906669 819042806897627222215001)
            ·
              refine ⟨614282105173220416661251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819042806897627222215001 614282105173220416661251)
              ·
                refine ⟨921423157759830624991877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614282105173220416661251 921423157759830624991877)
                ·
                  refine ⟨172766842079968242185977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921423157759830624991877 172766842079968242185977)
                  ·
                    rfl

theorem cell20_378520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_378520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378520 prefixEnd_378520 := by exact prefixLift 378520
  have htrace : WordTrace (prefixWord ++ tailWord_378520) baseStart_378520 baseEnd_378520 := by
    simpa [prefixWord, tailWord_378520, baseEnd_378520] using wordTrace_append hprefix tailTrace_378520
  have hstable : (prefixWord ++ tailWord_378520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378520).length < 2 ^ (prefixWord ++ tailWord_378520).sum := by decide
  have hdescent : baseEnd_378520 < baseStart_378520 := by decide
  rcases family_descends (prefixWord ++ tailWord_378520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378586 : List Nat := [3, 1, 1, 2, 2, 3, 1, 7]
def baseStart_378586 : Nat := 118140960795 + 378586 * 2 ^ 59
def prefixEnd_378586 : Nat := 4983230072969 + 3 ^ 40 * 378586 * 2
def baseEnd_378586 : Nat := 57598988759455115328569

theorem tailTrace_378586 : CollatzResearch.WordTrace tailWord_378586 prefixEnd_378586 57598988759455115328569 := by
  unfold tailWord_378586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3452041451613763546568903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9205443870970036124183741 3452041451613763546568903)
  ·
    refine ⟨5178062177420645319853355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3452041451613763546568903 5178062177420645319853355)
    ·
      refine ⟨7767093266130967979780033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5178062177420645319853355 7767093266130967979780033)
      ·
        refine ⟨5825319949598225984835025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7767093266130967979780033 5825319949598225984835025)
        ·
          refine ⟨4368989962198669488626269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5825319949598225984835025 4368989962198669488626269)
          ·
            refine ⟨1638371235824501058234851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4368989962198669488626269 1638371235824501058234851)
            ·
              refine ⟨2457556853736751587352277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638371235824501058234851 2457556853736751587352277)
              ·
                refine ⟨57598988759455115328569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2457556853736751587352277 57598988759455115328569)
                ·
                  rfl

theorem cell20_378586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_378586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378586 prefixEnd_378586 := by exact prefixLift 378586
  have htrace : WordTrace (prefixWord ++ tailWord_378586) baseStart_378586 baseEnd_378586 := by
    simpa [prefixWord, tailWord_378586, baseEnd_378586] using wordTrace_append hprefix tailTrace_378586
  have hstable : (prefixWord ++ tailWord_378586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378586).length < 2 ^ (prefixWord ++ tailWord_378586).sum := by decide
  have hdescent : baseEnd_378586 < baseStart_378586 := by decide
  rcases family_descends (prefixWord ++ tailWord_378586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378648 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 3]
def baseStart_378648 : Nat := 118140960795 + 378648 * 2 ^ 59
def prefixEnd_378648 : Nat := 4983230072969 + 3 ^ 40 * 378648 * 2
def baseEnd_378648 : Nat := 172825264767768685918787

theorem tailTrace_378648 : CollatzResearch.WordTrace tailWord_378648 prefixEnd_378648 172825264767768685918787 := by
  unfold tailWord_378648
  simp only [CollatzResearch.WordTrace]
  refine ⟨6905213566115219387516299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9206951421486959183355065 6905213566115219387516299)
  ·
    refine ⟨10357820349172829081274449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6905213566115219387516299 10357820349172829081274449)
    ·
      refine ⟨7768365261879621810955837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10357820349172829081274449 7768365261879621810955837)
      ·
        refine ⟨2913136973204858179108439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7768365261879621810955837 2913136973204858179108439)
        ·
          refine ⟨4369705459807287268662659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2913136973204858179108439 4369705459807287268662659)
          ·
            refine ⟨6554558189710930902993989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4369705459807287268662659 6554558189710930902993989)
            ·
              refine ⟨1228979660570799544311373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6554558189710930902993989 1228979660570799544311373)
              ·
                refine ⟨460867372714049829116765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1228979660570799544311373 460867372714049829116765)
                ·
                  refine ⟨172825264767768685918787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460867372714049829116765 172825264767768685918787)
                  ·
                    rfl

theorem cell20_378648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_378648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378648 prefixEnd_378648 := by exact prefixLift 378648
  have htrace : WordTrace (prefixWord ++ tailWord_378648) baseStart_378648 baseEnd_378648 := by
    simpa [prefixWord, tailWord_378648, baseEnd_378648] using wordTrace_append hprefix tailTrace_378648
  have hstable : (prefixWord ++ tailWord_378648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378648).length < 2 ^ (prefixWord ++ tailWord_378648).sum := by decide
  have hdescent : baseEnd_378648 < baseStart_378648 := by decide
  rcases family_descends (prefixWord ++ tailWord_378648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378654 : List Nat := [4, 3, 2, 2, 1, 1, 3, 4]
def baseStart_378654 : Nat := 118140960795 + 378654 * 2 ^ 59
def prefixEnd_378654 : Nat := 4983230072969 + 3 ^ 40 * 378654 * 2
def baseEnd_378654 : Nat := 57609334443753110572921

theorem tailTrace_378654 : CollatzResearch.WordTrace tailWord_378654 prefixEnd_378654 57609334443753110572921 := by
  unfold tailWord_378654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726330746276087724968877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9207097313472467866500677 1726330746276087724968877)
  ·
    refine ⟨647374029853532896863329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1726330746276087724968877 647374029853532896863329)
    ·
      refine ⟨485530522390149672647497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 647374029853532896863329 485530522390149672647497)
      ·
        refine ⟨364147891792612254485623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485530522390149672647497 364147891792612254485623)
        ·
          refine ⟨546221837688918381728435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364147891792612254485623 546221837688918381728435)
          ·
            refine ⟨819332756533377572592653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546221837688918381728435 819332756533377572592653)
            ·
              refine ⟨307249783700016589722245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 819332756533377572592653 307249783700016589722245)
              ·
                refine ⟨57609334443753110572921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307249783700016589722245 57609334443753110572921)
                ·
                  rfl

theorem cell20_378654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_378654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378654 prefixEnd_378654 := by exact prefixLift 378654
  have htrace : WordTrace (prefixWord ++ tailWord_378654) baseStart_378654 baseEnd_378654 := by
    simpa [prefixWord, tailWord_378654, baseEnd_378654] using wordTrace_append hprefix tailTrace_378654
  have hstable : (prefixWord ++ tailWord_378654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378654).length < 2 ^ (prefixWord ++ tailWord_378654).sum := by decide
  have hdescent : baseEnd_378654 < baseStart_378654 := by decide
  rcases family_descends (prefixWord ++ tailWord_378654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378655 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_378655 : Nat := 118140960795 + 378655 * 2 ^ 59
def prefixEnd_378655 : Nat := 4983230072969 + 3 ^ 40 * 378655 * 2
def baseEnd_378655 : Nat := 172828459758507772685425

theorem tailTrace_378655 : CollatzResearch.WordTrace tailWord_378655 prefixEnd_378655 172828459758507772685425 := by
  unfold tailWord_378655
  simp only [CollatzResearch.WordTrace]
  refine ⟨13810682443205078970537419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9207121628803385980358279 13810682443205078970537419)
  ·
    refine ⟨20716023664807618455806129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13810682443205078970537419 20716023664807618455806129)
    ·
      refine ⟨15537017748605713841854597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20716023664807618455806129 15537017748605713841854597)
      ·
        refine ⟨2913190827863571345347737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15537017748605713841854597 2913190827863571345347737)
        ·
          refine ⟨2184893120897678509010803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2913190827863571345347737 2184893120897678509010803)
          ·
            refine ⟨3277339681346517763516205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184893120897678509010803 3277339681346517763516205)
            ·
              refine ⟨1229002380504944161318577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3277339681346517763516205 1229002380504944161318577)
              ·
                refine ⟨921751785378708120988933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1229002380504944161318577 921751785378708120988933)
                ·
                  refine ⟨172828459758507772685425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921751785378708120988933 172828459758507772685425)
                  ·
                    rfl

theorem cell20_378655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_378655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378655 prefixEnd_378655 := by exact prefixLift 378655
  have htrace : WordTrace (prefixWord ++ tailWord_378655) baseStart_378655 baseEnd_378655 := by
    simpa [prefixWord, tailWord_378655, baseEnd_378655] using wordTrace_append hprefix tailTrace_378655
  have hstable : (prefixWord ++ tailWord_378655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378655).length < 2 ^ (prefixWord ++ tailWord_378655).sum := by decide
  have hdescent : baseEnd_378655 < baseStart_378655 := by decide
  rcases family_descends (prefixWord ++ tailWord_378655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378693 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 4]
def baseStart_378693 : Nat := 118140960795 + 378693 * 2 ^ 59
def prefixEnd_378693 : Nat := 4983230072969 + 3 ^ 40 * 378693 * 2
def baseEnd_378693 : Nat := 172845803993948529418603

theorem tailTrace_378693 : CollatzResearch.WordTrace tailWord_378693 prefixEnd_378693 172845803993948529418603 := by
  unfold tailWord_378693
  simp only [CollatzResearch.WordTrace]
  refine ⟨13812068417067411460420733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9208045611378274306947155 13812068417067411460420733)
  ·
    refine ⟨5179525656400279297657775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13812068417067411460420733 5179525656400279297657775)
    ·
      refine ⟨7769288484600418946486663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5179525656400279297657775 7769288484600418946486663)
      ·
        refine ⟨11653932726900628419729995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7769288484600418946486663 11653932726900628419729995)
        ·
          refine ⟨17480899090350942629594993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11653932726900628419729995 17480899090350942629594993)
          ·
            refine ⟨13110674317763206972196245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17480899090350942629594993 13110674317763206972196245)
            ·
              refine ⟨614562858645150326821699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13110674317763206972196245 614562858645150326821699)
              ·
                refine ⟨921844287967725490232549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614562858645150326821699 921844287967725490232549)
                ·
                  refine ⟨172845803993948529418603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921844287967725490232549 172845803993948529418603)
                  ·
                    rfl

theorem cell20_378693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_378693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378693 prefixEnd_378693 := by exact prefixLift 378693
  have htrace : WordTrace (prefixWord ++ tailWord_378693) baseStart_378693 baseEnd_378693 := by
    simpa [prefixWord, tailWord_378693, baseEnd_378693] using wordTrace_append hprefix tailTrace_378693
  have hstable : (prefixWord ++ tailWord_378693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378693).length < 2 ^ (prefixWord ++ tailWord_378693).sum := by decide
  have hdescent : baseEnd_378693 < baseStart_378693 := by decide
  rcases family_descends (prefixWord ++ tailWord_378693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378745 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_378745 : Nat := 118140960795 + 378745 * 2 ^ 59
def prefixEnd_378745 : Nat := 4983230072969 + 3 ^ 40 * 378745 * 2
def baseEnd_378745 : Nat := 172869538210867459685057

theorem tailTrace_378745 : CollatzResearch.WordTrace tailWord_378745 prefixEnd_378745 172869538210867459685057 := by
  unfold tailWord_378745
  simp only [CollatzResearch.WordTrace]
  refine ⟨13813965012879024341313689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9209310008586016227542459 13813965012879024341313689)
  ·
    refine ⟨10360473759659268255985267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13813965012879024341313689 10360473759659268255985267)
    ·
      refine ⟨15540710639488902383977901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10360473759659268255985267 15540710639488902383977901)
      ·
        refine ⟨5827766489808338393991713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15540710639488902383977901 5827766489808338393991713)
        ·
          refine ⟨4370824867356253795493785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5827766489808338393991713 4370824867356253795493785)
          ·
            refine ⟨3278118650517190346620339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4370824867356253795493785 3278118650517190346620339)
            ·
              refine ⟨4917177975775785519930509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3278118650517190346620339 4917177975775785519930509)
              ·
                refine ⟨1843941740915919569973941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4917177975775785519930509 1843941740915919569973941)
                ·
                  refine ⟨172869538210867459685057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1843941740915919569973941 172869538210867459685057)
                  ·
                    rfl

theorem cell20_378745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_378745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378745 prefixEnd_378745 := by exact prefixLift 378745
  have htrace : WordTrace (prefixWord ++ tailWord_378745) baseStart_378745 baseEnd_378745 := by
    simpa [prefixWord, tailWord_378745, baseEnd_378745] using wordTrace_append hprefix tailTrace_378745
  have hstable : (prefixWord ++ tailWord_378745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378745).length < 2 ^ (prefixWord ++ tailWord_378745).sum := by decide
  have hdescent : baseEnd_378745 < baseStart_378745 := by decide
  rcases family_descends (prefixWord ++ tailWord_378745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378841 : List Nat := [1, 2, 1, 2, 6, 1, 2, 3, 2]
def baseStart_378841 : Nat := 118140960795 + 378841 * 2 ^ 59
def prefixEnd_378841 : Nat := 4983230072969 + 3 ^ 40 * 378841 * 2
def baseEnd_378841 : Nat := 172913355226717792484665

theorem tailTrace_378841 : CollatzResearch.WordTrace tailWord_378841 prefixEnd_378841 172913355226717792484665 := by
  unfold tailWord_378841
  simp only [CollatzResearch.WordTrace]
  refine ⟨13817466420531232736808377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9211644280354155157872251 13817466420531232736808377)
  ·
    refine ⟨10363099815398424552606283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13817466420531232736808377 10363099815398424552606283)
    ·
      refine ⟨15544649723097636828909425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10363099815398424552606283 15544649723097636828909425)
      ·
        refine ⟨11658487292323227621682069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15544649723097636828909425 11658487292323227621682069)
        ·
          refine ⟨546491591827651294766347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11658487292323227621682069 546491591827651294766347)
          ·
            refine ⟨819737387741476942149521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546491591827651294766347 819737387741476942149521)
            ·
              refine ⟨614803040806107706612141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819737387741476942149521 614803040806107706612141)
              ·
                refine ⟨230551140302290389979553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 614803040806107706612141 230551140302290389979553)
                ·
                  refine ⟨172913355226717792484665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230551140302290389979553 172913355226717792484665)
                  ·
                    rfl

theorem cell20_378841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_378841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378841 prefixEnd_378841 := by exact prefixLift 378841
  have htrace : WordTrace (prefixWord ++ tailWord_378841) baseStart_378841 baseEnd_378841 := by
    simpa [prefixWord, tailWord_378841, baseEnd_378841] using wordTrace_append hprefix tailTrace_378841
  have hstable : (prefixWord ++ tailWord_378841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378841).length < 2 ^ (prefixWord ++ tailWord_378841).sum := by decide
  have hdescent : baseEnd_378841 < baseStart_378841 := by decide
  rcases family_descends (prefixWord ++ tailWord_378841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378862 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_378862 : Nat := 118140960795 + 378862 * 2 ^ 59
def prefixEnd_378862 : Nat := 4983230072969 + 3 ^ 40 * 378862 * 2
def baseEnd_378862 : Nat := 172922940198935052784579

theorem tailTrace_378862 : CollatzResearch.WordTrace tailWord_378862 prefixEnd_378862 172922940198935052784579 := by
  unfold tailWord_378862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1727279044181894165415355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9212154902303435548881893 1727279044181894165415355)
  ·
    refine ⟨2590918566272841248123033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1727279044181894165415355 2590918566272841248123033)
    ·
      refine ⟨1943188924704630936092275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2590918566272841248123033 1943188924704630936092275)
      ·
        refine ⟨2914783387056946404138413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943188924704630936092275 2914783387056946404138413)
        ·
          refine ⟨1093043770146354901551905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2914783387056946404138413 1093043770146354901551905)
          ·
            refine ⟨819782827609766176163929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1093043770146354901551905 819782827609766176163929)
            ·
              refine ⟨614837120707324632122947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819782827609766176163929 614837120707324632122947)
              ·
                refine ⟨922255681060986948184421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614837120707324632122947 922255681060986948184421)
                ·
                  refine ⟨172922940198935052784579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 922255681060986948184421 172922940198935052784579)
                  ·
                    rfl

theorem cell20_378862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_378862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378862 prefixEnd_378862 := by exact prefixLift 378862
  have htrace : WordTrace (prefixWord ++ tailWord_378862) baseStart_378862 baseEnd_378862 := by
    simpa [prefixWord, tailWord_378862, baseEnd_378862] using wordTrace_append hprefix tailTrace_378862
  have hstable : (prefixWord ++ tailWord_378862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378862).length < 2 ^ (prefixWord ++ tailWord_378862).sum := by decide
  have hdescent : baseEnd_378862 < baseStart_378862 := by decide
  rcases family_descends (prefixWord ++ tailWord_378862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378914 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_378914 : Nat := 118140960795 + 378914 * 2 ^ 59
def prefixEnd_378914 : Nat := 4983230072969 + 3 ^ 40 * 378914 * 2
def baseEnd_378914 : Nat := 172946674415853983051033

theorem tailTrace_378914 : CollatzResearch.WordTrace tailWord_378914 prefixEnd_378914 172946674415853983051033 := by
  unfold tailWord_378914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3455032237316691551053949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9213419299511177469477197 3455032237316691551053949)
  ·
    refine ⟨1295637088993759331645231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3455032237316691551053949 1295637088993759331645231)
    ·
      refine ⟨1943455633490638997467847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1295637088993759331645231 1943455633490638997467847)
      ·
        refine ⟨2915183450235958496201771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943455633490638997467847 2915183450235958496201771)
        ·
          refine ⟨4372775175353937744302657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915183450235958496201771 4372775175353937744302657)
          ·
            refine ⟨3279581381515453308226993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4372775175353937744302657 3279581381515453308226993)
            ·
              refine ⟨2459686036136589981170245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3279581381515453308226993 2459686036136589981170245)
              ·
                refine ⟨461191131775610621469421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2459686036136589981170245 461191131775610621469421)
                ·
                  refine ⟨172946674415853983051033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461191131775610621469421 172946674415853983051033)
                  ·
                    rfl

theorem cell20_378914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_378914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378914 prefixEnd_378914 := by exact prefixLift 378914
  have htrace : WordTrace (prefixWord ++ tailWord_378914) baseStart_378914 baseEnd_378914 := by
    simpa [prefixWord, tailWord_378914, baseEnd_378914] using wordTrace_append hprefix tailTrace_378914
  have hstable : (prefixWord ++ tailWord_378914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378914).length < 2 ^ (prefixWord ++ tailWord_378914).sum := by decide
  have hdescent : baseEnd_378914 < baseStart_378914 := by decide
  rcases family_descends (prefixWord ++ tailWord_378914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378917 : List Nat := [1, 3, 1, 2, 2, 4, 3, 2, 2]
def baseStart_378917 : Nat := 118140960795 + 378917 * 2 ^ 59
def prefixEnd_378917 : Nat := 4983230072969 + 3 ^ 40 * 378917 * 2
def baseEnd_378917 : Nat := 172948043697599305951021

theorem tailTrace_378917 : CollatzResearch.WordTrace tailWord_378917 prefixEnd_378917 172948043697599305951021 := by
  unfold tailWord_378917
  simp only [CollatzResearch.WordTrace]
  refine ⟨13820238368255897716575005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9213492245503931811050003 13820238368255897716575005)
  ·
    refine ⟨5182589388095961643715627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13820238368255897716575005 5182589388095961643715627)
    ·
      refine ⟨7773884082143942465573441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5182589388095961643715627 7773884082143942465573441)
      ·
        refine ⟨5830413061607956849180081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7773884082143942465573441 5830413061607956849180081)
        ·
          refine ⟨4372809796205967636885061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5830413061607956849180081 4372809796205967636885061)
          ·
            refine ⟨819901836788618931915949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4372809796205967636885061 819901836788618931915949)
            ·
              refine ⟨307463188795732099468481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 819901836788618931915949 307463188795732099468481)
              ·
                refine ⟨230597391596799074601361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307463188795732099468481 230597391596799074601361)
                ·
                  refine ⟨172948043697599305951021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230597391596799074601361 172948043697599305951021)
                  ·
                    rfl

theorem cell20_378917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_378917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378917 prefixEnd_378917 := by exact prefixLift 378917
  have htrace : WordTrace (prefixWord ++ tailWord_378917) baseStart_378917 baseEnd_378917 := by
    simpa [prefixWord, tailWord_378917, baseEnd_378917] using wordTrace_append hprefix tailTrace_378917
  have hstable : (prefixWord ++ tailWord_378917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378917).length < 2 ^ (prefixWord ++ tailWord_378917).sum := by decide
  have hdescent : baseEnd_378917 < baseStart_378917 := by decide
  rcases family_descends (prefixWord ++ tailWord_378917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378928 : List Nat := [2, 1, 1, 1, 2, 6, 2, 5]
def baseStart_378928 : Nat := 118140960795 + 378928 * 2 ^ 59
def prefixEnd_378928 : Nat := 4983230072969 + 3 ^ 40 * 378928 * 2
def baseEnd_378928 : Nat := 57651021465777385528103

theorem tailTrace_378928 : CollatzResearch.WordTrace tailWord_378928 prefixEnd_378928 57651021465777385528103 := by
  unfold tailWord_378928
  simp only [CollatzResearch.WordTrace]
  refine ⟨6910319785608023297612719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9213759714144031063483625 6910319785608023297612719)
  ·
    refine ⟨10365479678412034946419079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6910319785608023297612719 10365479678412034946419079)
    ·
      refine ⟨15548219517618052419628619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10365479678412034946419079 15548219517618052419628619)
      ·
        refine ⟨23322329276427078629442929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15548219517618052419628619 23322329276427078629442929)
        ·
          refine ⟨17491746957320308972082197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23322329276427078629442929 17491746957320308972082197)
          ·
            refine ⟨819925638624389483066353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17491746957320308972082197 819925638624389483066353)
            ·
              refine ⟨614944228968292112299765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819925638624389483066353 614944228968292112299765)
              ·
                refine ⟨57651021465777385528103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 614944228968292112299765 57651021465777385528103)
                ·
                  rfl

theorem cell20_378928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_378928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378928 prefixEnd_378928 := by exact prefixLift 378928
  have htrace : WordTrace (prefixWord ++ tailWord_378928) baseStart_378928 baseEnd_378928 := by
    simpa [prefixWord, tailWord_378928, baseEnd_378928] using wordTrace_append hprefix tailTrace_378928
  have hstable : (prefixWord ++ tailWord_378928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378928).length < 2 ^ (prefixWord ++ tailWord_378928).sum := by decide
  have hdescent : baseEnd_378928 < baseStart_378928 := by decide
  rcases family_descends (prefixWord ++ tailWord_378928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378972 : List Nat := [2, 2, 4, 1, 1, 4, 2, 2, 2]
def baseStart_378972 : Nat := 118140960795 + 378972 * 2 ^ 59
def prefixEnd_378972 : Nat := 4983230072969 + 3 ^ 40 * 378972 * 2
def baseEnd_378972 : Nat := 172973147196263559117463

theorem tailTrace_378972 : CollatzResearch.WordTrace tailWord_378972 prefixEnd_378972 172973147196263559117463 := by
  unfold tailWord_378972
  simp only [CollatzResearch.WordTrace]
  refine ⟨6911122191528321054913585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9214829588704428073218113 6911122191528321054913585)
  ·
    refine ⟨5183341643646240791185189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6911122191528321054913585 5183341643646240791185189)
    ·
      refine ⟨971876558183670148347223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5183341643646240791185189 971876558183670148347223)
      ·
        refine ⟨1457814837275505222520835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 971876558183670148347223 1457814837275505222520835)
        ·
          refine ⟨2186722255913257833781253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457814837275505222520835 2186722255913257833781253)
          ·
            refine ⟨410010422983735843833985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2186722255913257833781253 410010422983735843833985)
            ·
              refine ⟨307507817237801882875489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410010422983735843833985 307507817237801882875489)
              ·
                refine ⟨230630862928351412156617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307507817237801882875489 230630862928351412156617)
                ·
                  refine ⟨172973147196263559117463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230630862928351412156617 172973147196263559117463)
                  ·
                    rfl

theorem cell20_378972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_378972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378972 prefixEnd_378972 := by exact prefixLift 378972
  have htrace : WordTrace (prefixWord ++ tailWord_378972) baseStart_378972 baseEnd_378972 := by
    simpa [prefixWord, tailWord_378972, baseEnd_378972] using wordTrace_append hprefix tailTrace_378972
  have hstable : (prefixWord ++ tailWord_378972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378972).length < 2 ^ (prefixWord ++ tailWord_378972).sum := by decide
  have hdescent : baseEnd_378972 < baseStart_378972 := by decide
  rcases family_descends (prefixWord ++ tailWord_378972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378976 : List Nat := [2, 1, 1, 3, 2, 4, 1, 4, 2]
def baseStart_378976 : Nat := 118140960795 + 378976 * 2 ^ 59
def prefixEnd_378976 : Nat := 4983230072969 + 3 ^ 40 * 378976 * 2
def baseEnd_378976 : Nat := 172974972905257322984113

theorem tailTrace_378976 : CollatzResearch.WordTrace tailWord_378976 prefixEnd_378976 172974972905257322984113 := by
  unfold tailWord_378976
  simp only [CollatzResearch.WordTrace]
  refine ⟨6911195137521075396486391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9214926850028100528648521 6911195137521075396486391)
  ·
    refine ⟨10366792706281613094729587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6911195137521075396486391 10366792706281613094729587)
    ·
      refine ⟨15550189059422419642094381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10366792706281613094729587 15550189059422419642094381)
      ·
        refine ⟨5831320897283407365785393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15550189059422419642094381 5831320897283407365785393)
        ·
          refine ⟨4373490672962555524339045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5831320897283407365785393 4373490672962555524339045)
          ·
            refine ⟨820029501180479160813571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4373490672962555524339045 820029501180479160813571)
            ·
              refine ⟨1230044251770718741220357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820029501180479160813571 1230044251770718741220357)
              ·
                refine ⟨230633297207009763978817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1230044251770718741220357 230633297207009763978817)
                ·
                  refine ⟨172974972905257322984113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230633297207009763978817 172974972905257322984113)
                  ·
                    rfl

theorem cell20_378976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_378976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378976 prefixEnd_378976 := by exact prefixLift 378976
  have htrace : WordTrace (prefixWord ++ tailWord_378976) baseStart_378976 baseEnd_378976 := by
    simpa [prefixWord, tailWord_378976, baseEnd_378976] using wordTrace_append hprefix tailTrace_378976
  have hstable : (prefixWord ++ tailWord_378976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378976).length < 2 ^ (prefixWord ++ tailWord_378976).sum := by decide
  have hdescent : baseEnd_378976 < baseStart_378976 := by decide
  rcases family_descends (prefixWord ++ tailWord_378976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378990 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_378990 : Nat := 118140960795 + 378990 * 2 ^ 59
def prefixEnd_378990 : Nat := 4983230072969 + 3 ^ 40 * 378990 * 2
def baseEnd_378990 : Nat := 172981362886735496517389

theorem tailTrace_378990 : CollatzResearch.WordTrace tailWord_378990 prefixEnd_378990 172981362886735496517389 := by
  unfold tailWord_378990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1727862612123928897997803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9215267264660954122654949 1727862612123928897997803)
  ·
    refine ⟨2591793918185893346996705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1727862612123928897997803 2591793918185893346996705)
    ·
      refine ⟨1943845438639420010247529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2591793918185893346996705 1943845438639420010247529)
      ·
        refine ⟨1457884078979565007685647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1943845438639420010247529 1457884078979565007685647)
        ·
          refine ⟨2186826118469347511528471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457884078979565007685647 2186826118469347511528471)
          ·
            refine ⟨3280239177704021267292707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186826118469347511528471 3280239177704021267292707)
            ·
              refine ⟨4920358766556031900939061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280239177704021267292707 4920358766556031900939061)
              ·
                refine ⟨461283634364627990713037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4920358766556031900939061 461283634364627990713037)
                ·
                  refine ⟨172981362886735496517389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461283634364627990713037 172981362886735496517389)
                  ·
                    rfl

theorem cell20_378990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_378990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_378990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_378990 prefixEnd_378990 := by exact prefixLift 378990
  have htrace : WordTrace (prefixWord ++ tailWord_378990) baseStart_378990 baseEnd_378990 := by
    simpa [prefixWord, tailWord_378990, baseEnd_378990] using wordTrace_append hprefix tailTrace_378990
  have hstable : (prefixWord ++ tailWord_378990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378990).length < 2 ^ (prefixWord ++ tailWord_378990).sum := by decide
  have hdescent : baseEnd_378990 < baseStart_378990 := by decide
  rcases family_descends (prefixWord ++ tailWord_378990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379035 : List Nat := [1, 1, 1, 1, 1, 1, 2, 10, 2]
def baseStart_379035 : Nat := 118140960795 + 379035 * 2 ^ 59
def prefixEnd_379035 : Nat := 4983230072969 + 3 ^ 40 * 379035 * 2
def baseEnd_379035 : Nat := 173001902112915340017205

theorem tailTrace_379035 : CollatzResearch.WordTrace tailWord_379035 prefixEnd_379035 173001902112915340017205 := by
  unfold tailWord_379035
  simp only [CollatzResearch.WordTrace]
  refine ⟨13824542181828403869370559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9216361454552269246247039 13824542181828403869370559)
  ·
    refine ⟨20736813272742605804055839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13824542181828403869370559 20736813272742605804055839)
    ·
      refine ⟨31105219909113908706083759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20736813272742605804055839 31105219909113908706083759)
      ·
        refine ⟨46657829863670863059125639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31105219909113908706083759 46657829863670863059125639)
        ·
          refine ⟨69986744795506294588688459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46657829863670863059125639 69986744795506294588688459)
          ·
            refine ⟨104980117193259441883032689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69986744795506294588688459 104980117193259441883032689)
            ·
              refine ⟨78735087894944581412274517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104980117193259441883032689 78735087894944581412274517)
              ·
                refine ⟨230669202817220453356273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 78735087894944581412274517 230669202817220453356273)
                ·
                  refine ⟨173001902112915340017205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230669202817220453356273 173001902112915340017205)
                  ·
                    rfl

theorem cell20_379035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 2].length) (baseStart_379035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379035 prefixEnd_379035 := by exact prefixLift 379035
  have htrace : WordTrace (prefixWord ++ tailWord_379035) baseStart_379035 baseEnd_379035 := by
    simpa [prefixWord, tailWord_379035, baseEnd_379035] using wordTrace_append hprefix tailTrace_379035
  have hstable : (prefixWord ++ tailWord_379035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379035).length < 2 ^ (prefixWord ++ tailWord_379035).sum := by decide
  have hdescent : baseEnd_379035 < baseStart_379035 := by decide
  rcases family_descends (prefixWord ++ tailWord_379035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379087 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 3]
def baseStart_379087 : Nat := 118140960795 + 379087 * 2 ^ 59
def prefixEnd_379087 : Nat := 4983230072969 + 3 ^ 40 * 379087 * 2
def baseEnd_379087 : Nat := 173025636329834270283659

theorem tailTrace_379087 : CollatzResearch.WordTrace tailWord_379087 prefixEnd_379087 173025636329834270283659 := by
  unfold tailWord_379087
  simp only [CollatzResearch.WordTrace]
  refine ⟨13826438777640016750263515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9217625851760011166842343 13826438777640016750263515)
  ·
    refine ⟨20739658166460025125395273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13826438777640016750263515 20739658166460025125395273)
    ·
      refine ⟨15554743624845018844046455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20739658166460025125395273 15554743624845018844046455)
      ·
        refine ⟨23332115437267528266069683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15554743624845018844046455 23332115437267528266069683)
        ·
          refine ⟨34998173155901292399104525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23332115437267528266069683 34998173155901292399104525)
          ·
            refine ⟨13124314933462984649664197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34998173155901292399104525 13124314933462984649664197)
            ·
              refine ⟨2460809050024309621812037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13124314933462984649664197 2460809050024309621812037)
              ·
                refine ⟨461401696879558054089757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2460809050024309621812037 461401696879558054089757)
                ·
                  refine ⟨173025636329834270283659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461401696879558054089757 173025636329834270283659)
                  ·
                    rfl

theorem cell20_379087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 3].length) (baseStart_379087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379087 prefixEnd_379087 := by exact prefixLift 379087
  have htrace : WordTrace (prefixWord ++ tailWord_379087) baseStart_379087 baseEnd_379087 := by
    simpa [prefixWord, tailWord_379087, baseEnd_379087] using wordTrace_append hprefix tailTrace_379087
  have hstable : (prefixWord ++ tailWord_379087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379087).length < 2 ^ (prefixWord ++ tailWord_379087).sum := by decide
  have hdescent : baseEnd_379087 < baseStart_379087 := by decide
  rcases family_descends (prefixWord ++ tailWord_379087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379090 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_379090 : Nat := 118140960795 + 379090 * 2 ^ 59
def prefixEnd_379090 : Nat := 4983230072969 + 3 ^ 40 * 379090 * 2
def baseEnd_379090 : Nat := 173027005611579593183647

theorem tailTrace_379090 : CollatzResearch.WordTrace tailWord_379090 prefixEnd_379090 173027005611579593183647 := by
  unfold tailWord_379090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456637049157287065655681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9217698797752765508415149 3456637049157287065655681)
  ·
    refine ⟨2592477786867965299241761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3456637049157287065655681 2592477786867965299241761)
    ·
      refine ⟨1944358340150973974431321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2592477786867965299241761 1944358340150973974431321)
      ·
        refine ⟨1458268755113230480823491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1944358340150973974431321 1458268755113230480823491)
        ·
          refine ⟨2187403132669845721235237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458268755113230480823491 2187403132669845721235237)
          ·
            refine ⟨410138087375596072731607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2187403132669845721235237 410138087375596072731607)
            ·
              refine ⟨615207131063394109097411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410138087375596072731607 615207131063394109097411)
              ·
                refine ⟨922810696595091163646117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615207131063394109097411 922810696595091163646117)
                ·
                  refine ⟨173027005611579593183647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 922810696595091163646117 173027005611579593183647)
                  ·
                    rfl

theorem cell20_379090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_379090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379090 prefixEnd_379090 := by exact prefixLift 379090
  have htrace : WordTrace (prefixWord ++ tailWord_379090) baseStart_379090 baseEnd_379090 := by
    simpa [prefixWord, tailWord_379090, baseEnd_379090] using wordTrace_append hprefix tailTrace_379090
  have hstable : (prefixWord ++ tailWord_379090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379090).length < 2 ^ (prefixWord ++ tailWord_379090).sum := by decide
  have hdescent : baseEnd_379090 < baseStart_379090 := by decide
  rcases family_descends (prefixWord ++ tailWord_379090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379100 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 3]
def baseStart_379100 : Nat := 118140960795 + 379100 * 2 ^ 59
def prefixEnd_379100 : Nat := 4983230072969 + 3 ^ 40 * 379100 * 2
def baseEnd_379100 : Nat := 173031569884064002850273

theorem tailTrace_379100 : CollatzResearch.WordTrace tailWord_379100 prefixEnd_379100 173031569884064002850273 := by
  unfold tailWord_379100
  simp only [CollatzResearch.WordTrace]
  refine ⟨6913456463296459985243377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9217941951061946646991169 6913456463296459985243377)
  ·
    refine ⟨5185092347472344988932533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6913456463296459985243377 5185092347472344988932533)
    ·
      refine ⟨486102407575532342712425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5185092347472344988932533 486102407575532342712425)
      ·
        refine ⟨364576805681649257034319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486102407575532342712425 364576805681649257034319)
        ·
          refine ⟨546865208522473885551479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364576805681649257034319 546865208522473885551479)
          ·
            refine ⟨820297812783710828327219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546865208522473885551479 820297812783710828327219)
            ·
              refine ⟨1230446719175566242490829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820297812783710828327219 1230446719175566242490829)
              ·
                refine ⟨461417519690837340934061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1230446719175566242490829 461417519690837340934061)
                ·
                  refine ⟨173031569884064002850273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461417519690837340934061 173031569884064002850273)
                  ·
                    rfl

theorem cell20_379100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_379100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379100 prefixEnd_379100 := by exact prefixLift 379100
  have htrace : WordTrace (prefixWord ++ tailWord_379100) baseStart_379100 baseEnd_379100 := by
    simpa [prefixWord, tailWord_379100, baseEnd_379100] using wordTrace_append hprefix tailTrace_379100
  have hstable : (prefixWord ++ tailWord_379100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379100).length < 2 ^ (prefixWord ++ tailWord_379100).sum := by decide
  have hdescent : baseEnd_379100 < baseStart_379100 := by decide
  rcases family_descends (prefixWord ++ tailWord_379100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379145 : List Nat := [1, 2, 1, 1, 3, 6, 2, 2, 2]
def baseStart_379145 : Nat := 118140960795 + 379145 * 2 ^ 59
def prefixEnd_379145 : Nat := 4983230072969 + 3 ^ 40 * 379145 * 2
def baseEnd_379145 : Nat := 173052109110243846350089

theorem tailTrace_379145 : CollatzResearch.WordTrace tailWord_379145 prefixEnd_379145 173052109110243846350089 := by
  unfold tailWord_379145
  simp only [CollatzResearch.WordTrace]
  refine ⟨13828554211429892655874889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9219036140953261770583259 13828554211429892655874889)
  ·
    refine ⟨10371415658572419491906167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13828554211429892655874889 10371415658572419491906167)
    ·
      refine ⟨15557123487858629237859251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10371415658572419491906167 15557123487858629237859251)
      ·
        refine ⟨23335685231787943856788877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15557123487858629237859251 23335685231787943856788877)
        ·
          refine ⟨8750881961920478946295829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23335685231787943856788877 8750881961920478946295829)
          ·
            refine ⟨410197591965022450607617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8750881961920478946295829 410197591965022450607617)
            ·
              refine ⟨307648193973766837955713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410197591965022450607617 307648193973766837955713)
              ·
                refine ⟨230736145480325128466785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307648193973766837955713 230736145480325128466785)
                ·
                  refine ⟨173052109110243846350089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230736145480325128466785 173052109110243846350089)
                  ·
                    rfl

theorem cell20_379145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_379145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379145 prefixEnd_379145 := by exact prefixLift 379145
  have htrace : WordTrace (prefixWord ++ tailWord_379145) baseStart_379145 baseEnd_379145 := by
    simpa [prefixWord, tailWord_379145, baseEnd_379145] using wordTrace_append hprefix tailTrace_379145
  have hstable : (prefixWord ++ tailWord_379145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379145).length < 2 ^ (prefixWord ++ tailWord_379145).sum := by decide
  have hdescent : baseEnd_379145 < baseStart_379145 := by decide
  rcases family_descends (prefixWord ++ tailWord_379145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379163 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 3]
def baseStart_379163 : Nat := 118140960795 + 379163 * 2 ^ 59
def prefixEnd_379163 : Nat := 4983230072969 + 3 ^ 40 * 379163 * 2
def baseEnd_379163 : Nat := 173060324800715783750015

theorem tailTrace_379163 : CollatzResearch.WordTrace tailWord_379163 prefixEnd_379163 173060324800715783750015 := by
  unfold tailWord_379163
  simp only [CollatzResearch.WordTrace]
  refine ⟨13829210725364681730030143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9219473816909787820020095 13829210725364681730030143)
  ·
    refine ⟨20743816088047022595045215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13829210725364681730030143 20743816088047022595045215)
    ·
      refine ⟨31115724132070533892567823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20743816088047022595045215 31115724132070533892567823)
      ·
        refine ⟨46673586198105800838851735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31115724132070533892567823 46673586198105800838851735)
        ·
          refine ⟨70010379297158701258277603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46673586198105800838851735 70010379297158701258277603)
          ·
            refine ⟨105015568945738051887416405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70010379297158701258277603 105015568945738051887416405)
            ·
              refine ⟨1230651198582867795555661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 105015568945738051887416405 1230651198582867795555661)
              ·
                refine ⟨461494199468575423333373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1230651198582867795555661 461494199468575423333373)
                ·
                  refine ⟨173060324800715783750015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461494199468575423333373 173060324800715783750015)
                  ·
                    rfl

theorem cell20_379163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 3].length) (baseStart_379163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379163 prefixEnd_379163 := by exact prefixLift 379163
  have htrace : WordTrace (prefixWord ++ tailWord_379163) baseStart_379163 baseEnd_379163 := by
    simpa [prefixWord, tailWord_379163, baseEnd_379163] using wordTrace_append hprefix tailTrace_379163
  have hstable : (prefixWord ++ tailWord_379163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379163).length < 2 ^ (prefixWord ++ tailWord_379163).sum := by decide
  have hdescent : baseEnd_379163 < baseStart_379163 := by decide
  rcases family_descends (prefixWord ++ tailWord_379163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379166 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_379166 : Nat := 118140960795 + 379166 * 2 ^ 59
def prefixEnd_379166 : Nat := 4983230072969 + 3 ^ 40 * 379166 * 2
def baseEnd_379166 : Nat := 173061694082461106650003

theorem tailTrace_379166 : CollatzResearch.WordTrace tailWord_379166 prefixEnd_379166 173061694082461106650003 := by
  unfold tailWord_379166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728665018044226655298669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9219546762902542161592901 1728665018044226655298669)
  ·
    refine ⟨648249381766584995737001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1728665018044226655298669 648249381766584995737001)
    ·
      refine ⟨486187036324938746802751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 648249381766584995737001 486187036324938746802751)
      ·
        refine ⟨729280554487408120204127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486187036324938746802751 729280554487408120204127)
        ·
          refine ⟨1093920831731112180306191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729280554487408120204127 1093920831731112180306191)
          ·
            refine ⟨1640881247596668270459287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093920831731112180306191 1640881247596668270459287)
            ·
              refine ⟨2461321871395002405688931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640881247596668270459287 2461321871395002405688931)
              ·
                refine ⟨3691982807092503608533397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2461321871395002405688931 3691982807092503608533397)
                ·
                  refine ⟨173061694082461106650003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3691982807092503608533397 173061694082461106650003)
                  ·
                    rfl

theorem cell20_379166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_379166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379166 prefixEnd_379166 := by exact prefixLift 379166
  have htrace : WordTrace (prefixWord ++ tailWord_379166) baseStart_379166 baseEnd_379166 := by
    simpa [prefixWord, tailWord_379166, baseEnd_379166] using wordTrace_append hprefix tailTrace_379166
  have hstable : (prefixWord ++ tailWord_379166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379166).length < 2 ^ (prefixWord ++ tailWord_379166).sum := by decide
  have hdescent : baseEnd_379166 < baseStart_379166 := by decide
  rcases family_descends (prefixWord ++ tailWord_379166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379173 : List Nat := [1, 3, 1, 2, 5, 1, 3, 4]
def baseStart_379173 : Nat := 118140960795 + 379173 * 2 ^ 59
def prefixEnd_379173 : Nat := 4983230072969 + 3 ^ 40 * 379173 * 2
def baseEnd_379173 : Nat := 57688296357733397805547

theorem tailTrace_379173 : CollatzResearch.WordTrace tailWord_379173 prefixEnd_379173 57688296357733397805547 := by
  unfold tailWord_379173
  simp only [CollatzResearch.WordTrace]
  refine ⟨13829575455328453437894173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9219716970218968958596115 13829575455328453437894173)
  ·
    refine ⟨5186090795748170039210315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13829575455328453437894173 5186090795748170039210315)
    ·
      refine ⟨7779136193622255058815473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5186090795748170039210315 7779136193622255058815473)
      ·
        refine ⟨5834352145216691294111605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7779136193622255058815473 5834352145216691294111605)
        ·
          refine ⟨546970513614064808822963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5834352145216691294111605 546970513614064808822963)
          ·
            refine ⟨820455770421097213234445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546970513614064808822963 820455770421097213234445)
            ·
              refine ⟨307670913907911454962917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 820455770421097213234445 307670913907911454962917)
              ·
                refine ⟨57688296357733397805547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307670913907911454962917 57688296357733397805547)
                ·
                  rfl

theorem cell20_379173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 4].length) (baseStart_379173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379173 prefixEnd_379173 := by exact prefixLift 379173
  have htrace : WordTrace (prefixWord ++ tailWord_379173) baseStart_379173 baseEnd_379173 := by
    simpa [prefixWord, tailWord_379173, baseEnd_379173] using wordTrace_append hprefix tailTrace_379173
  have hstable : (prefixWord ++ tailWord_379173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379173).length < 2 ^ (prefixWord ++ tailWord_379173).sum := by decide
  have hdescent : baseEnd_379173 < baseStart_379173 := by decide
  rcases family_descends (prefixWord ++ tailWord_379173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379208 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_379208 : Nat := 118140960795 + 379208 * 2 ^ 59
def prefixEnd_379208 : Nat := 4983230072969 + 3 ^ 40 * 379208 * 2
def baseEnd_379208 : Nat := 173080864026895627249831

theorem tailTrace_379208 : CollatzResearch.WordTrace tailWord_379208 prefixEnd_379208 173080864026895627249831 := by
  unfold tailWord_379208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915426005100827207709139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9220568006801102943612185 6915426005100827207709139)
  ·
    refine ⟨10373139007651240811563709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6915426005100827207709139 10373139007651240811563709)
    ·
      refine ⟨3889927127869215304336391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10373139007651240811563709 3889927127869215304336391)
      ·
        refine ⟨5834890691803822956504587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889927127869215304336391 5834890691803822956504587)
        ·
          refine ⟨8752336037705734434756881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5834890691803822956504587 8752336037705734434756881)
          ·
            refine ⟨6564252028279300826067661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8752336037705734434756881 6564252028279300826067661)
            ·
              refine ⟨2461594510604737809775373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6564252028279300826067661 2461594510604737809775373)
              ·
                refine ⟨923097941476776678665765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2461594510604737809775373 923097941476776678665765)
                ·
                  refine ⟨173080864026895627249831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 923097941476776678665765 173080864026895627249831)
                  ·
                    rfl

theorem cell20_379208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_379208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379208 prefixEnd_379208 := by exact prefixLift 379208
  have htrace : WordTrace (prefixWord ++ tailWord_379208) baseStart_379208 baseEnd_379208 := by
    simpa [prefixWord, tailWord_379208, baseEnd_379208] using wordTrace_append hprefix tailTrace_379208
  have hstable : (prefixWord ++ tailWord_379208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379208).length < 2 ^ (prefixWord ++ tailWord_379208).sum := by decide
  have hdescent : baseEnd_379208 < baseStart_379208 := by decide
  rcases family_descends (prefixWord ++ tailWord_379208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379232 : List Nat := [2, 1, 1, 3, 5, 1, 1, 6]
def baseStart_379232 : Nat := 118140960795 + 379232 * 2 ^ 59
def prefixEnd_379232 : Nat := 4983230072969 + 3 ^ 40 * 379232 * 2
def baseEnd_379232 : Nat := 57697272760286070149911

theorem tailTrace_379232 : CollatzResearch.WordTrace tailWord_379232 prefixEnd_379232 57697272760286070149911 := by
  unfold tailWord_379232
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915863681057353257145975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9221151574743137676194633 6915863681057353257145975)
  ·
    refine ⟨10373795521586029885718963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6915863681057353257145975 10373795521586029885718963)
    ·
      refine ⟨15560693282379044828578445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10373795521586029885718963 15560693282379044828578445)
      ·
        refine ⟨5835259980892141810716917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15560693282379044828578445 5835259980892141810716917)
        ·
          refine ⟨547055623208638294754711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5835259980892141810716917 547055623208638294754711)
          ·
            refine ⟨820583434812957442132067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547055623208638294754711 820583434812957442132067)
            ·
              refine ⟨1230875152219436163198101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820583434812957442132067 1230875152219436163198101)
              ·
                refine ⟨57697272760286070149911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1230875152219436163198101 57697272760286070149911)
                ·
                  rfl

theorem cell20_379232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_379232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379232 prefixEnd_379232 := by exact prefixLift 379232
  have htrace : WordTrace (prefixWord ++ tailWord_379232) baseStart_379232 baseEnd_379232 := by
    simpa [prefixWord, tailWord_379232, baseEnd_379232] using wordTrace_append hprefix tailTrace_379232
  have hstable : (prefixWord ++ tailWord_379232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379232).length < 2 ^ (prefixWord ++ tailWord_379232).sum := by decide
  have hdescent : baseEnd_379232 < baseStart_379232 := by decide
  rcases family_descends (prefixWord ++ tailWord_379232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379239 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_379239 : Nat := 118140960795 + 379239 * 2 ^ 59
def prefixEnd_379239 : Nat := 4983230072969 + 3 ^ 40 * 379239 * 2
def baseEnd_379239 : Nat := 173095013271597297216371

theorem tailTrace_379239 : CollatzResearch.WordTrace tailWord_379239 prefixEnd_379239 173095013271597297216371 := by
  unfold tailWord_379239
  simp only [CollatzResearch.WordTrace]
  refine ⟨13831982673089346709796771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9221321782059564473197847 13831982673089346709796771)
  ·
    refine ⟨20747974009634020064695157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13831982673089346709796771 20747974009634020064695157)
    ·
      refine ⟨1945122563403189381065171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20747974009634020064695157 1945122563403189381065171)
      ·
        refine ⟨2917683845104784071597757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1945122563403189381065171 2917683845104784071597757)
        ·
          refine ⟨1094131441914294026849159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2917683845104784071597757 1094131441914294026849159)
          ·
            refine ⟨1641197162871441040273739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094131441914294026849159 1641197162871441040273739)
            ·
              refine ⟨2461795744307161560410609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641197162871441040273739 2461795744307161560410609)
              ·
                refine ⟨1846346808230371170307957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2461795744307161560410609 1846346808230371170307957)
                ·
                  refine ⟨173095013271597297216371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1846346808230371170307957 173095013271597297216371)
                  ·
                    rfl

theorem cell20_379239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_379239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379239 prefixEnd_379239 := by exact prefixLift 379239
  have htrace : WordTrace (prefixWord ++ tailWord_379239) baseStart_379239 baseEnd_379239 := by
    simpa [prefixWord, tailWord_379239, baseEnd_379239] using wordTrace_append hprefix tailTrace_379239
  have hstable : (prefixWord ++ tailWord_379239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379239).length < 2 ^ (prefixWord ++ tailWord_379239).sum := by decide
  have hdescent : baseEnd_379239 < baseStart_379239 := by decide
  rcases family_descends (prefixWord ++ tailWord_379239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379266 : List Nat := [3, 4, 2, 1, 2, 1, 2, 5]
def baseStart_379266 : Nat := 118140960795 + 379266 * 2 ^ 59
def prefixEnd_379266 : Nat := 4983230072969 + 3 ^ 40 * 379266 * 2
def baseEnd_379266 : Nat := 57702445602435067772087

theorem tailTrace_379266 : CollatzResearch.WordTrace tailWord_379266 prefixEnd_379266 57702445602435067772087 := by
  unfold tailWord_379266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3458241860997882580257413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9221978295994353547353101 3458241860997882580257413)
  ·
    refine ⟨648420348937102983798265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3458241860997882580257413 648420348937102983798265)
    ·
      refine ⟨486315261702827237848699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 648420348937102983798265 486315261702827237848699)
      ·
        refine ⟨729472892554240856773049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486315261702827237848699 729472892554240856773049)
        ·
          refine ⟨547104669415680642579787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 729472892554240856773049 547104669415680642579787)
          ·
            refine ⟨820657004123520963869681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547104669415680642579787 820657004123520963869681)
            ·
              refine ⟨615492753092640722902261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820657004123520963869681 615492753092640722902261)
              ·
                refine ⟨57702445602435067772087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 615492753092640722902261 57702445602435067772087)
                ·
                  rfl

theorem cell20_379266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_379266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379266 prefixEnd_379266 := by exact prefixLift 379266
  have htrace : WordTrace (prefixWord ++ tailWord_379266) baseStart_379266 baseEnd_379266 := by
    simpa [prefixWord, tailWord_379266, baseEnd_379266] using wordTrace_append hprefix tailTrace_379266
  have hstable : (prefixWord ++ tailWord_379266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379266).length < 2 ^ (prefixWord ++ tailWord_379266).sum := by decide
  have hdescent : baseEnd_379266 < baseStart_379266 := by decide
  rcases family_descends (prefixWord ++ tailWord_379266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379273 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 3]
def baseStart_379273 : Nat := 118140960795 + 379273 * 2 ^ 59
def prefixEnd_379273 : Nat := 4983230072969 + 3 ^ 40 * 379273 * 2
def baseEnd_379273 : Nat := 173110531798044290082899

theorem tailTrace_379273 : CollatzResearch.WordTrace tailWord_379273 prefixEnd_379273 173110531798044290082899 := by
  unfold tailWord_379273
  simp only [CollatzResearch.WordTrace]
  refine ⟨13833222754966170516534473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9222148503310780344356315 13833222754966170516534473)
  ·
    refine ⟨10374917066224627887400855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13833222754966170516534473 10374917066224627887400855)
    ·
      refine ⟨15562375599336941831101283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10374917066224627887400855 15562375599336941831101283)
      ·
        refine ⟨23343563399005412746651925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15562375599336941831101283 23343563399005412746651925)
        ·
          refine ⟨1094229534328378722499309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23343563399005412746651925 1094229534328378722499309)
          ·
            refine ⟨410336075373142020937241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1094229534328378722499309 410336075373142020937241)
            ·
              refine ⟨307752056529856515702931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410336075373142020937241 307752056529856515702931)
              ·
                refine ⟨461628084794784773554397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307752056529856515702931 461628084794784773554397)
                ·
                  refine ⟨173110531798044290082899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461628084794784773554397 173110531798044290082899)
                  ·
                    rfl

theorem cell20_379273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_379273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379273 prefixEnd_379273 := by exact prefixLift 379273
  have htrace : WordTrace (prefixWord ++ tailWord_379273) baseStart_379273 baseEnd_379273 := by
    simpa [prefixWord, tailWord_379273, baseEnd_379273] using wordTrace_append hprefix tailTrace_379273
  have hstable : (prefixWord ++ tailWord_379273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379273).length < 2 ^ (prefixWord ++ tailWord_379273).sum := by decide
  have hdescent : baseEnd_379273 < baseStart_379273 := by decide
  rcases family_descends (prefixWord ++ tailWord_379273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379301 : List Nat := [1, 3, 1, 2, 1, 1, 4, 5, 2]
def baseStart_379301 : Nat := 118140960795 + 379301 * 2 ^ 59
def prefixEnd_379301 : Nat := 4983230072969 + 3 ^ 40 * 379301 * 2
def baseEnd_379301 : Nat := 173123311761000637149451

theorem tailTrace_379301 : CollatzResearch.WordTrace tailWord_379301 prefixEnd_379301 173123311761000637149451 := by
  unfold tailWord_379301
  simp only [CollatzResearch.WordTrace]
  refine ⟨13834243998864731298553757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9222829332576487532369171 13834243998864731298553757)
  ·
    refine ⟨5187841499574274236957659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13834243998864731298553757 5187841499574274236957659)
    ·
      refine ⟨7781762249361411355436489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5187841499574274236957659 7781762249361411355436489)
      ·
        refine ⟨5836321687021058516577367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7781762249361411355436489 5836321687021058516577367)
        ·
          refine ⟨8754482530531587774866051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5836321687021058516577367 8754482530531587774866051)
          ·
            refine ⟨13131723795797381662299077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8754482530531587774866051 13131723795797381662299077)
            ·
              refine ⟨2462198211712009061681077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13131723795797381662299077 2462198211712009061681077)
              ·
                refine ⟨230831082348000849532601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2462198211712009061681077 230831082348000849532601)
                ·
                  refine ⟨173123311761000637149451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230831082348000849532601 173123311761000637149451)
                  ·
                    rfl

theorem cell20_379301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_379301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379301 prefixEnd_379301 := by exact prefixLift 379301
  have htrace : WordTrace (prefixWord ++ tailWord_379301) baseStart_379301 baseEnd_379301 := by
    simpa [prefixWord, tailWord_379301, baseEnd_379301] using wordTrace_append hprefix tailTrace_379301
  have hstable : (prefixWord ++ tailWord_379301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379301).length < 2 ^ (prefixWord ++ tailWord_379301).sum := by decide
  have hdescent : baseEnd_379301 < baseStart_379301 := by decide
  rcases family_descends (prefixWord ++ tailWord_379301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379367 : List Nat := [1, 1, 5, 2, 1, 1, 9]
def baseStart_379367 : Nat := 118140960795 + 379367 * 2 ^ 59
def prefixEnd_379367 : Nat := 4983230072969 + 3 ^ 40 * 379367 * 2
def baseEnd_379367 : Nat := 19239270662155304549909

theorem tailTrace_379367 : CollatzResearch.WordTrace tailWord_379367 prefixEnd_379367 19239270662155304549909 := by
  unfold tailWord_379367
  simp only [CollatzResearch.WordTrace]
  refine ⟨13836651216625624570456355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9224434144417083046970903 13836651216625624570456355)
  ·
    refine ⟨20754976824938436855684533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13836651216625624570456355 20754976824938436855684533)
    ·
      refine ⟨1945779077337978455220425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20754976824938436855684533 1945779077337978455220425)
      ·
        refine ⟨1459334308003483841415319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1945779077337978455220425 1459334308003483841415319)
        ·
          refine ⟨2189001462005225762122979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459334308003483841415319 2189001462005225762122979)
          ·
            refine ⟨3283502193007838643184469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189001462005225762122979 3283502193007838643184469)
            ·
              refine ⟨19239270662155304549909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3283502193007838643184469 19239270662155304549909)
              ·
                rfl

theorem cell20_379367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 9].length) (baseStart_379367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379367 prefixEnd_379367 := by exact prefixLift 379367
  have htrace : WordTrace (prefixWord ++ tailWord_379367) baseStart_379367 baseEnd_379367 := by
    simpa [prefixWord, tailWord_379367, baseEnd_379367] using wordTrace_append hprefix tailTrace_379367
  have hstable : (prefixWord ++ tailWord_379367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379367).length < 2 ^ (prefixWord ++ tailWord_379367).sum := by decide
  have hdescent : baseEnd_379367 < baseStart_379367 := by decide
  rcases family_descends (prefixWord ++ tailWord_379367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379370 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_379370 : Nat := 118140960795 + 379370 * 2 ^ 59
def prefixEnd_379370 : Nat := 4983230072969 + 3 ^ 40 * 379370 * 2
def baseEnd_379370 : Nat := 173154805241143063849169

theorem tailTrace_379370 : CollatzResearch.WordTrace tailWord_379370 prefixEnd_379370 173154805241143063849169 := by
  unfold tailWord_379370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459190158903689020703891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9224507090409837388543709 3459190158903689020703891)
  ·
    refine ⟨5188785238355533531055837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3459190158903689020703891 5188785238355533531055837)
    ·
      refine ⟨1945794464383325074145939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5188785238355533531055837 1945794464383325074145939)
      ·
        refine ⟨2918691696574987611218909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1945794464383325074145939 2918691696574987611218909)
        ·
          refine ⟨1094509386215620354207091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2918691696574987611218909 1094509386215620354207091)
          ·
            refine ⟨1641764079323430531310637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094509386215620354207091 1641764079323430531310637)
            ·
              refine ⟨615661529746286449241489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1641764079323430531310637 615661529746286449241489)
              ·
                refine ⟨461746147309714836931117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615661529746286449241489 461746147309714836931117)
                ·
                  refine ⟨173154805241143063849169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461746147309714836931117 173154805241143063849169)
                  ·
                    rfl

theorem cell20_379370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_379370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379370 prefixEnd_379370 := by exact prefixLift 379370
  have htrace : WordTrace (prefixWord ++ tailWord_379370) baseStart_379370 baseEnd_379370 := by
    simpa [prefixWord, tailWord_379370, baseEnd_379370] using wordTrace_append hprefix tailTrace_379370
  have hstable : (prefixWord ++ tailWord_379370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379370).length < 2 ^ (prefixWord ++ tailWord_379370).sum := by decide
  have hdescent : baseEnd_379370 < baseStart_379370 := by decide
  rcases family_descends (prefixWord ++ tailWord_379370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379377 : List Nat := [1, 2, 2, 2, 3, 1, 1, 6, 2]
def baseStart_379377 : Nat := 118140960795 + 379377 * 2 ^ 59
def prefixEnd_379377 : Nat := 4983230072969 + 3 ^ 40 * 379377 * 2
def baseEnd_379377 : Nat := 173158000231882150615807

theorem tailTrace_379377 : CollatzResearch.WordTrace tailWord_379377 prefixEnd_379377 173158000231882150615807 := by
  unfold tailWord_379377
  simp only [CollatzResearch.WordTrace]
  refine ⟨13837015946589396278320385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9224677297726264185546923 13837015946589396278320385)
  ·
    refine ⟨10377761959942047208740289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13837015946589396278320385 10377761959942047208740289)
    ·
      refine ⟨7783321469956535406555217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10377761959942047208740289 7783321469956535406555217)
      ·
        refine ⟨5837491102467401554916413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7783321469956535406555217 5837491102467401554916413)
        ·
          refine ⟨2189059163425275583093655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5837491102467401554916413 2189059163425275583093655)
          ·
            refine ⟨3283588745137913374640483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189059163425275583093655 3283588745137913374640483)
            ·
              refine ⟨4925383117706870061960725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283588745137913374640483 4925383117706870061960725)
              ·
                refine ⟨230877333642509534154409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4925383117706870061960725 230877333642509534154409)
                ·
                  refine ⟨173158000231882150615807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230877333642509534154409 173158000231882150615807)
                  ·
                    rfl

theorem cell20_379377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_379377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379377 prefixEnd_379377 := by exact prefixLift 379377
  have htrace : WordTrace (prefixWord ++ tailWord_379377) baseStart_379377 baseEnd_379377 := by
    simpa [prefixWord, tailWord_379377, baseEnd_379377] using wordTrace_append hprefix tailTrace_379377
  have hstable : (prefixWord ++ tailWord_379377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379377).length < 2 ^ (prefixWord ++ tailWord_379377).sum := by decide
  have hdescent : baseEnd_379377 < baseStart_379377 := by decide
  rcases family_descends (prefixWord ++ tailWord_379377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379428 : List Nat := [2, 3, 1, 5, 1, 1, 3, 2, 2]
def baseStart_379428 : Nat := 118140960795 + 379428 * 2 ^ 59
def prefixEnd_379428 : Nat := 4983230072969 + 3 ^ 40 * 379428 * 2
def baseEnd_379428 : Nat := 173181278021552639915599

theorem tailTrace_379428 : CollatzResearch.WordTrace tailWord_379428 prefixEnd_379428 173181278021552639915599 := by
  unfold tailWord_379428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919438034702315994213469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9225917379603087992284625 6919438034702315994213469)
  ·
    refine ⟨2594789263013368497830051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6919438034702315994213469 2594789263013368497830051)
    ·
      refine ⟨3892183894520052746745077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2594789263013368497830051 3892183894520052746745077)
      ·
        refine ⟨364892240111254945007351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3892183894520052746745077 364892240111254945007351)
        ·
          refine ⟨547338360166882417511027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364892240111254945007351 547338360166882417511027)
          ·
            refine ⟨821007540250323626266541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547338360166882417511027 821007540250323626266541)
            ·
              refine ⟨307877827593871359849953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 821007540250323626266541 307877827593871359849953)
              ·
                refine ⟨230908370695403519887465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307877827593871359849953 230908370695403519887465)
                ·
                  refine ⟨173181278021552639915599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230908370695403519887465 173181278021552639915599)
                  ·
                    rfl

theorem cell20_379428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_379428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379428 prefixEnd_379428 := by exact prefixLift 379428
  have htrace : WordTrace (prefixWord ++ tailWord_379428) baseStart_379428 baseEnd_379428 := by
    simpa [prefixWord, tailWord_379428, baseEnd_379428] using wordTrace_append hprefix tailTrace_379428
  have hstable : (prefixWord ++ tailWord_379428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379428).length < 2 ^ (prefixWord ++ tailWord_379428).sum := by decide
  have hdescent : baseEnd_379428 < baseStart_379428 := by decide
  rcases family_descends (prefixWord ++ tailWord_379428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379432 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 4]
def baseStart_379432 : Nat := 118140960795 + 379432 * 2 ^ 59
def prefixEnd_379432 : Nat := 4983230072969 + 3 ^ 40 * 379432 * 2
def baseEnd_379432 : Nat := 173183103730546403782249

theorem tailTrace_379432 : CollatzResearch.WordTrace tailWord_379432 prefixEnd_379432 173183103730546403782249 := by
  unfold tailWord_379432
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919510980695070335786275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9226014640926760447715033 6919510980695070335786275)
  ·
    refine ⟨10379266471042605503679413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6919510980695070335786275 10379266471042605503679413)
    ·
      refine ⟨973056231660244265969945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10379266471042605503679413 973056231660244265969945)
      ·
        refine ⟨729792173745183199477459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 973056231660244265969945 729792173745183199477459)
        ·
          refine ⟨1094688260617774799216189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729792173745183199477459 1094688260617774799216189)
          ·
            refine ⟨410508097731665549706071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1094688260617774799216189 410508097731665549706071)
            ·
              refine ⟨615762146597498324559107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410508097731665549706071 615762146597498324559107)
              ·
                refine ⟨923643219896247486838661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615762146597498324559107 923643219896247486838661)
                ·
                  refine ⟨173183103730546403782249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 923643219896247486838661 173183103730546403782249)
                  ·
                    rfl

theorem cell20_379432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_379432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379432 prefixEnd_379432 := by exact prefixLift 379432
  have htrace : WordTrace (prefixWord ++ tailWord_379432) baseStart_379432 baseEnd_379432 := by
    simpa [prefixWord, tailWord_379432, baseEnd_379432] using wordTrace_append hprefix tailTrace_379432
  have hstable : (prefixWord ++ tailWord_379432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379432).length < 2 ^ (prefixWord ++ tailWord_379432).sum := by decide
  have hdescent : baseEnd_379432 < baseStart_379432 := by decide
  rcases family_descends (prefixWord ++ tailWord_379432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379443 : List Nat := [1, 1, 1, 2, 4, 2, 4, 5]
def baseStart_379443 : Nat := 118140960795 + 379443 * 2 ^ 59
def prefixEnd_379443 : Nat := 4983230072969 + 3 ^ 40 * 379443 * 2
def baseEnd_379443 : Nat := 57729374810093084805179

theorem tailTrace_379443 : CollatzResearch.WordTrace tailWord_379443 prefixEnd_379443 57729374810093084805179 := by
  unfold tailWord_379443
  simp only [CollatzResearch.WordTrace]
  refine ⟨13839423164350289550222983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9226282109566859700148655 13839423164350289550222983)
  ·
    refine ⟨20759134746525434325334475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13839423164350289550222983 20759134746525434325334475)
    ·
      refine ⟨31138702119788151488001713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20759134746525434325334475 31138702119788151488001713)
      ·
        refine ⟨23354026589841113616001285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31138702119788151488001713 23354026589841113616001285)
        ·
          refine ⟨4378879985595208803000241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23354026589841113616001285 4378879985595208803000241)
          ·
            refine ⟨3284159989196406602250181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4378879985595208803000241 3284159989196406602250181)
            ·
              refine ⟨615779997974326237921909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3284159989196406602250181 615779997974326237921909)
              ·
                refine ⟨57729374810093084805179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 615779997974326237921909 57729374810093084805179)
                ·
                  rfl

theorem cell20_379443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_379443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379443 prefixEnd_379443 := by exact prefixLift 379443
  have htrace : WordTrace (prefixWord ++ tailWord_379443) baseStart_379443 baseEnd_379443 := by
    simpa [prefixWord, tailWord_379443, baseEnd_379443] using wordTrace_append hprefix tailTrace_379443
  have hstable : (prefixWord ++ tailWord_379443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379443).length < 2 ^ (prefixWord ++ tailWord_379443).sum := by decide
  have hdescent : baseEnd_379443 < baseStart_379443 := by decide
  rcases family_descends (prefixWord ++ tailWord_379443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379488 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_379488 : Nat := 118140960795 + 379488 * 2 ^ 59
def prefixEnd_379488 : Nat := 4983230072969 + 3 ^ 40 * 379488 * 2
def baseEnd_379488 : Nat := 173208663656459097915353

theorem tailTrace_379488 : CollatzResearch.WordTrace tailWord_379488 prefixEnd_379488 173208663656459097915353 := by
  unfold tailWord_379488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6920532224593631117805559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9227376299458174823740745 6920532224593631117805559)
  ·
    refine ⟨10380798336890446676708339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6920532224593631117805559 10380798336890446676708339)
    ·
      refine ⟨15571197505335670015062509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10380798336890446676708339 15571197505335670015062509)
      ·
        refine ⟨5839199064500876255648441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15571197505335670015062509 5839199064500876255648441)
        ·
          refine ⟨4379399298375657191736331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5839199064500876255648441 4379399298375657191736331)
          ·
            refine ⟨6569098947563485787604497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4379399298375657191736331 6569098947563485787604497)
            ·
              refine ⟨4926824210672614340703373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6569098947563485787604497 4926824210672614340703373)
              ·
                refine ⟨1847559079002230377763765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4926824210672614340703373 1847559079002230377763765)
                ·
                  refine ⟨173208663656459097915353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1847559079002230377763765 173208663656459097915353)
                  ·
                    rfl

theorem cell20_379488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_379488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379488 prefixEnd_379488 := by exact prefixLift 379488
  have htrace : WordTrace (prefixWord ++ tailWord_379488) baseStart_379488 baseEnd_379488 := by
    simpa [prefixWord, tailWord_379488, baseEnd_379488] using wordTrace_append hprefix tailTrace_379488
  have hstable : (prefixWord ++ tailWord_379488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379488).length < 2 ^ (prefixWord ++ tailWord_379488).sum := by decide
  have hdescent : baseEnd_379488 < baseStart_379488 := by decide
  rcases family_descends (prefixWord ++ tailWord_379488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379491 : List Nat := [1, 1, 1, 5, 1, 2, 3, 4, 2]
def baseStart_379491 : Nat := 118140960795 + 379491 * 2 ^ 59
def prefixEnd_379491 : Nat := 4983230072969 + 3 ^ 40 * 379491 * 2
def baseEnd_379491 : Nat := 173210032938204420815341

theorem tailTrace_379491 : CollatzResearch.WordTrace tailWord_379491 prefixEnd_379491 173210032938204420815341 := by
  unfold tailWord_379491
  simp only [CollatzResearch.WordTrace]
  refine ⟨13841173868176393747970327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9227449245450929165313551 13841173868176393747970327)
  ·
    refine ⟨20761760802264590621955491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13841173868176393747970327 20761760802264590621955491)
    ·
      refine ⟨31142641203396885932933237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20761760802264590621955491 31142641203396885932933237)
      ·
        refine ⟨2919622612818458056212491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31142641203396885932933237 2919622612818458056212491)
        ·
          refine ⟨4379433919227687084318737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2919622612818458056212491 4379433919227687084318737)
          ·
            refine ⟨3284575439420765313239053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4379433919227687084318737 3284575439420765313239053)
            ·
              refine ⟨1231715789782786992464645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3284575439420765313239053 1231715789782786992464645)
              ·
                refine ⟨230946710584272561087121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1231715789782786992464645 230946710584272561087121)
                ·
                  refine ⟨173210032938204420815341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230946710584272561087121 173210032938204420815341)
                  ·
                    rfl

theorem cell20_379491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 2].length) (baseStart_379491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379491 prefixEnd_379491 := by exact prefixLift 379491
  have htrace : WordTrace (prefixWord ++ tailWord_379491) baseStart_379491 baseEnd_379491 := by
    simpa [prefixWord, tailWord_379491, baseEnd_379491] using wordTrace_append hprefix tailTrace_379491
  have hstable : (prefixWord ++ tailWord_379491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379491).length < 2 ^ (prefixWord ++ tailWord_379491).sum := by decide
  have hdescent : baseEnd_379491 < baseStart_379491 := by decide
  rcases family_descends (prefixWord ++ tailWord_379491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379546 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_379546 : Nat := 118140960795 + 379546 * 2 ^ 59
def prefixEnd_379546 : Nat := 4983230072969 + 3 ^ 40 * 379546 * 2
def baseEnd_379546 : Nat := 173235136436868673981783

theorem tailTrace_379546 : CollatzResearch.WordTrace tailWord_379546 prefixEnd_379546 173235136436868673981783 := by
  unfold tailWord_379546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3460794970744284535305623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9228786588651425427481661 3460794970744284535305623)
  ·
    refine ⟨5191192456116426802958435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3460794970744284535305623 5191192456116426802958435)
    ·
      refine ⟨7786788684174640204437653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5191192456116426802958435 7786788684174640204437653)
      ·
        refine ⟨365005719570686259583015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7786788684174640204437653 365005719570686259583015)
        ·
          refine ⟨547508579356029389374523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365005719570686259583015 547508579356029389374523)
          ·
            refine ⟨821262869034044084061785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547508579356029389374523 821262869034044084061785)
            ·
              refine ⟨615947151775533063046339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821262869034044084061785 615947151775533063046339)
              ·
                refine ⟨923920727663299594569509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615947151775533063046339 923920727663299594569509)
                ·
                  refine ⟨173235136436868673981783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 923920727663299594569509 173235136436868673981783)
                  ·
                    rfl

theorem cell20_379546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_379546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379546 prefixEnd_379546 := by exact prefixLift 379546
  have htrace : WordTrace (prefixWord ++ tailWord_379546) baseStart_379546 baseEnd_379546 := by
    simpa [prefixWord, tailWord_379546, baseEnd_379546] using wordTrace_append hprefix tailTrace_379546
  have hstable : (prefixWord ++ tailWord_379546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379546).length < 2 ^ (prefixWord ++ tailWord_379546).sum := by decide
  have hdescent : baseEnd_379546 < baseStart_379546 := by decide
  rcases family_descends (prefixWord ++ tailWord_379546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379584 : List Nat := [2, 1, 1, 2, 4, 4, 1, 3, 2]
def baseStart_379584 : Nat := 118140960795 + 379584 * 2 ^ 59
def prefixEnd_379584 : Nat := 4983230072969 + 3 ^ 40 * 379584 * 2
def baseEnd_379584 : Nat := 173252480672309430714961

theorem tailTrace_379584 : CollatzResearch.WordTrace tailWord_379584 prefixEnd_379584 173252480672309430714961 := by
  unfold tailWord_379584
  simp only [CollatzResearch.WordTrace]
  refine ⟨6922282928419735315552903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9229710571226313754070537 6922282928419735315552903)
  ·
    refine ⟨10383424392629602973329355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6922282928419735315552903 10383424392629602973329355)
    ·
      refine ⟨15575136588944404459994033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10383424392629602973329355 15575136588944404459994033)
      ·
        refine ⟨11681352441708303344995525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15575136588944404459994033 11681352441708303344995525)
        ·
          refine ⟨2190253582820306877186661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11681352441708303344995525 2190253582820306877186661)
          ·
            refine ⟨410672546778807539472499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2190253582820306877186661 410672546778807539472499)
            ·
              refine ⟨616008820168211309208749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410672546778807539472499 616008820168211309208749)
              ·
                refine ⟨231003307563079240953281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 616008820168211309208749 231003307563079240953281)
                ·
                  refine ⟨173252480672309430714961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231003307563079240953281 173252480672309430714961)
                  ·
                    rfl

theorem cell20_379584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_379584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379584 prefixEnd_379584 := by exact prefixLift 379584
  have htrace : WordTrace (prefixWord ++ tailWord_379584) baseStart_379584 baseEnd_379584 := by
    simpa [prefixWord, tailWord_379584, baseEnd_379584] using wordTrace_append hprefix tailTrace_379584
  have hstable : (prefixWord ++ tailWord_379584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379584).length < 2 ^ (prefixWord ++ tailWord_379584).sum := by decide
  have hdescent : baseEnd_379584 < baseStart_379584 := by decide
  rcases family_descends (prefixWord ++ tailWord_379584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379612 : List Nat := [2, 2, 5, 1, 1, 1, 1, 7]
def baseStart_379612 : Nat := 118140960795 + 379612 * 2 ^ 59
def prefixEnd_379612 : Nat := 4983230072969 + 3 ^ 40 * 379612 * 2
def baseEnd_379612 : Nat := 57755086878421925927171

theorem tailTrace_379612 : CollatzResearch.WordTrace tailWord_379612 prefixEnd_379612 57755086878421925927171 := by
  unfold tailWord_379612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6922793550369015706562545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9230391400492020942083393 6922793550369015706562545)
  ·
    refine ⟨5192095162776761779921909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6922793550369015706562545 5192095162776761779921909)
    ·
      refine ⟨486758921510321416867679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5192095162776761779921909 486758921510321416867679)
      ·
        refine ⟨730138382265482125301519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486758921510321416867679 730138382265482125301519)
        ·
          refine ⟨1095207573398223187952279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730138382265482125301519 1095207573398223187952279)
          ·
            refine ⟨1642811360097334781928419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095207573398223187952279 1642811360097334781928419)
            ·
              refine ⟨2464217040146002172892629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642811360097334781928419 2464217040146002172892629)
              ·
                refine ⟨57755086878421925927171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2464217040146002172892629 57755086878421925927171)
                ·
                  rfl

theorem cell20_379612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_379612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379612 prefixEnd_379612 := by exact prefixLift 379612
  have htrace : WordTrace (prefixWord ++ tailWord_379612) baseStart_379612 baseEnd_379612 := by
    simpa [prefixWord, tailWord_379612, baseEnd_379612] using wordTrace_append hprefix tailTrace_379612
  have hstable : (prefixWord ++ tailWord_379612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379612).length < 2 ^ (prefixWord ++ tailWord_379612).sum := by decide
  have hdescent : baseEnd_379612 < baseStart_379612 := by decide
  rcases family_descends (prefixWord ++ tailWord_379612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379688 : List Nat := [2, 1, 5, 1, 1, 1, 5, 4]
def baseStart_379688 : Nat := 118140960795 + 379688 * 2 ^ 59
def prefixEnd_379688 : Nat := 4983230072969 + 3 ^ 40 * 379688 * 2
def baseEnd_379688 : Nat := 57766649702049097082623

theorem tailTrace_379688 : CollatzResearch.WordTrace tailWord_379688 prefixEnd_379688 57766649702049097082623 := by
  unfold tailWord_379688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6924179524231348196445859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9232239365641797595261145 6924179524231348196445859)
  ·
    refine ⟨10386269286347022294668789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6924179524231348196445859 10386269286347022294668789)
    ·
      refine ⟨973712745595033340125199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10386269286347022294668789 973712745595033340125199)
      ·
        refine ⟨1460569118392550010187799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973712745595033340125199 1460569118392550010187799)
        ·
          refine ⟨2190853677588825015281699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460569118392550010187799 2190853677588825015281699)
          ·
            refine ⟨3286280516383237522922549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190853677588825015281699 3286280516383237522922549)
            ·
              refine ⟨308088798410928517773989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3286280516383237522922549 308088798410928517773989)
              ·
                refine ⟨57766649702049097082623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308088798410928517773989 57766649702049097082623)
                ·
                  rfl

theorem cell20_379688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_379688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379688 prefixEnd_379688 := by exact prefixLift 379688
  have htrace : WordTrace (prefixWord ++ tailWord_379688) baseStart_379688 baseEnd_379688 := by
    simpa [prefixWord, tailWord_379688, baseEnd_379688] using wordTrace_append hprefix tailTrace_379688
  have hstable : (prefixWord ++ tailWord_379688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379688).length < 2 ^ (prefixWord ++ tailWord_379688).sum := by decide
  have hdescent : baseEnd_379688 < baseStart_379688 := by decide
  rcases family_descends (prefixWord ++ tailWord_379688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379747 : List Nat := [1, 1, 1, 5, 3, 2, 1, 6]
def baseStart_379747 : Nat := 118140960795 + 379747 * 2 ^ 59
def prefixEnd_379747 : Nat := 4983230072969 + 3 ^ 40 * 379747 * 2
def baseEnd_379747 : Nat := 57775626104601769426987

theorem tailTrace_379747 : CollatzResearch.WordTrace tailWord_379747 prefixEnd_379747 57775626104601769426987 := by
  unfold tailWord_379747
  simp only [CollatzResearch.WordTrace]
  refine ⟨13850510955248949469289495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9233673970165966312859663 13850510955248949469289495)
  ·
    refine ⟨20775766432873424203934243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13850510955248949469289495 20775766432873424203934243)
    ·
      refine ⟨31163649649310136305901365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20775766432873424203934243 31163649649310136305901365)
      ·
        refine ⟨2921592154622825278678253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31163649649310136305901365 2921592154622825278678253)
        ·
          refine ⟨1095597057983559479504345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2921592154622825278678253 1095597057983559479504345)
          ·
            refine ⟨821697793487669609628259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095597057983559479504345 821697793487669609628259)
            ·
              refine ⟨1232546690231504414442389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821697793487669609628259 1232546690231504414442389)
              ·
                refine ⟨57775626104601769426987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1232546690231504414442389 57775626104601769426987)
                ·
                  rfl

theorem cell20_379747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_379747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379747 prefixEnd_379747 := by exact prefixLift 379747
  have htrace : WordTrace (prefixWord ++ tailWord_379747) baseStart_379747 baseEnd_379747 := by
    simpa [prefixWord, tailWord_379747, baseEnd_379747] using wordTrace_append hprefix tailTrace_379747
  have hstable : (prefixWord ++ tailWord_379747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379747).length < 2 ^ (prefixWord ++ tailWord_379747).sum := by decide
  have hdescent : baseEnd_379747 < baseStart_379747 := by decide
  rcases family_descends (prefixWord ++ tailWord_379747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379785 : List Nat := [1, 2, 1, 1, 5, 3, 2, 5]
def baseStart_379785 : Nat := 118140960795 + 379785 * 2 ^ 59
def prefixEnd_379785 : Nat := 4983230072969 + 3 ^ 40 * 379785 * 2
def baseEnd_379785 : Nat := 57781407516415355004713

theorem tailTrace_379785 : CollatzResearch.WordTrace tailWord_379785 prefixEnd_379785 57781407516415355004713 := by
  unfold tailWord_379785
  simp only [CollatzResearch.WordTrace]
  refine ⟨13851896929111281959172809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9234597952740854639448539 13851896929111281959172809)
  ·
    refine ⟨10388922696833461469379607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13851896929111281959172809 10388922696833461469379607)
    ·
      refine ⟨15583384045250192204069411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10388922696833461469379607 15583384045250192204069411)
      ·
        refine ⟨23375076067875288306104117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15583384045250192204069411 23375076067875288306104117)
        ·
          refine ⟨2191413381363308278697261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23375076067875288306104117 2191413381363308278697261)
          ·
            refine ⟨821780018011240604511473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2191413381363308278697261 821780018011240604511473)
            ·
              refine ⟨616335013508430453383605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821780018011240604511473 616335013508430453383605)
              ·
                refine ⟨57781407516415355004713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 616335013508430453383605 57781407516415355004713)
                ·
                  rfl

theorem cell20_379785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_379785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379785 prefixEnd_379785 := by exact prefixLift 379785
  have htrace : WordTrace (prefixWord ++ tailWord_379785) baseStart_379785 baseEnd_379785 := by
    simpa [prefixWord, tailWord_379785, baseEnd_379785] using wordTrace_append hprefix tailTrace_379785
  have hstable : (prefixWord ++ tailWord_379785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379785).length < 2 ^ (prefixWord ++ tailWord_379785).sum := by decide
  have hdescent : baseEnd_379785 < baseStart_379785 := by decide
  rcases family_descends (prefixWord ++ tailWord_379785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379799 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_379799 : Nat := 118140960795 + 379799 * 2 ^ 59
def prefixEnd_379799 : Nat := 4983230072969 + 3 ^ 40 * 379799 * 2
def baseEnd_379799 : Nat := 173350612530724238547415

theorem tailTrace_379799 : CollatzResearch.WordTrace tailWord_379799 prefixEnd_379799 173350612530724238547415 := by
  unfold tailWord_379799
  simp only [CollatzResearch.WordTrace]
  refine ⟨13852407551060562350182451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9234938367373708233454967 13852407551060562350182451)
  ·
    refine ⟨20778611326590843525273677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13852407551060562350182451 20778611326590843525273677)
    ·
      refine ⟨7791979247471566321977629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20778611326590843525273677 7791979247471566321977629)
      ·
        refine ⟨2921992217801837370741611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7791979247471566321977629 2921992217801837370741611)
        ·
          refine ⟨4382988326702756056112417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2921992217801837370741611 4382988326702756056112417)
          ·
            refine ⟨3287241245027067042084313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4382988326702756056112417 3287241245027067042084313)
            ·
              refine ⟨2465430933770300281563235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3287241245027067042084313 2465430933770300281563235)
              ·
                refine ⟨3698146400655450422344853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465430933770300281563235 3698146400655450422344853)
                ·
                  refine ⟨173350612530724238547415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3698146400655450422344853 173350612530724238547415)
                  ·
                    rfl

theorem cell20_379799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_379799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379799 prefixEnd_379799 := by exact prefixLift 379799
  have htrace : WordTrace (prefixWord ++ tailWord_379799) baseStart_379799 baseEnd_379799 := by
    simpa [prefixWord, tailWord_379799, baseEnd_379799] using wordTrace_append hprefix tailTrace_379799
  have hstable : (prefixWord ++ tailWord_379799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379799).length < 2 ^ (prefixWord ++ tailWord_379799).sum := by decide
  have hdescent : baseEnd_379799 < baseStart_379799 := by decide
  rcases family_descends (prefixWord ++ tailWord_379799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379833 : List Nat := [1, 2, 1, 4, 2, 3, 1, 4, 2]
def baseStart_379833 : Nat := 118140960795 + 379833 * 2 ^ 59
def prefixEnd_379833 : Nat := 4983230072969 + 3 ^ 40 * 379833 * 2
def baseEnd_379833 : Nat := 173366131057171231413943

theorem tailTrace_379833 : CollatzResearch.WordTrace tailWord_379833 prefixEnd_379833 173366131057171231413943 := by
  unfold tailWord_379833
  simp only [CollatzResearch.WordTrace]
  refine ⟨13853647632937386156920153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9235765088624924104613435 13853647632937386156920153)
  ·
    refine ⟨10390235724703039617690115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13853647632937386156920153 10390235724703039617690115)
    ·
      refine ⟨15585353587054559426535173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10390235724703039617690115 15585353587054559426535173)
      ·
        refine ⟨2922253797572729892475345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15585353587054559426535173 2922253797572729892475345)
        ·
          refine ⟨2191690348179547419356509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922253797572729892475345 2191690348179547419356509)
          ·
            refine ⟨821883880567330282258691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2191690348179547419356509 821883880567330282258691)
            ·
              refine ⟨1232825820850995423388037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821883880567330282258691 1232825820850995423388037)
              ·
                refine ⟨231154841409561641885257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1232825820850995423388037 231154841409561641885257)
                ·
                  refine ⟨173366131057171231413943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231154841409561641885257 173366131057171231413943)
                  ·
                    rfl

theorem cell20_379833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_379833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379833 prefixEnd_379833 := by exact prefixLift 379833
  have htrace : WordTrace (prefixWord ++ tailWord_379833) baseStart_379833 baseEnd_379833 := by
    simpa [prefixWord, tailWord_379833, baseEnd_379833] using wordTrace_append hprefix tailTrace_379833
  have hstable : (prefixWord ++ tailWord_379833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379833).length < 2 ^ (prefixWord ++ tailWord_379833).sum := by decide
  have hdescent : baseEnd_379833 < baseStart_379833 := by decide
  rcases family_descends (prefixWord ++ tailWord_379833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379846 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_379846 : Nat := 118140960795 + 379846 * 2 ^ 59
def prefixEnd_379846 : Nat := 4983230072969 + 3 ^ 40 * 379846 * 2
def baseEnd_379846 : Nat := 173372064611400963980557

theorem tailTrace_379846 : CollatzResearch.WordTrace tailWord_379846 prefixEnd_379846 173372064611400963980557 := by
  unfold tailWord_379846
  simp only [CollatzResearch.WordTrace]
  refine ⟨432941305684071543035731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9236081187926859584762261 432941305684071543035731)
  ·
    refine ⟨649411958526107314553597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 432941305684071543035731 649411958526107314553597)
    ·
      refine ⟨243529484447290242957599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 649411958526107314553597 243529484447290242957599)
      ·
        refine ⟨365294226670935364436399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243529484447290242957599 365294226670935364436399)
        ·
          refine ⟨547941340006403046654599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365294226670935364436399 547941340006403046654599)
          ·
            refine ⟨821912010009604569981899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547941340006403046654599 821912010009604569981899)
            ·
              refine ⟨1232868015014406854972849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821912010009604569981899 1232868015014406854972849)
              ·
                refine ⟨924651011260805141229637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232868015014406854972849 924651011260805141229637)
                ·
                  refine ⟨173372064611400963980557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924651011260805141229637 173372064611400963980557)
                  ·
                    rfl

theorem cell20_379846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_379846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379846 prefixEnd_379846 := by exact prefixLift 379846
  have htrace : WordTrace (prefixWord ++ tailWord_379846) baseStart_379846 baseEnd_379846 := by
    simpa [prefixWord, tailWord_379846, baseEnd_379846] using wordTrace_append hprefix tailTrace_379846
  have hstable : (prefixWord ++ tailWord_379846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379846).length < 2 ^ (prefixWord ++ tailWord_379846).sum := by decide
  have hdescent : baseEnd_379846 < baseStart_379846 := by decide
  rcases family_descends (prefixWord ++ tailWord_379846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379853 : List Nat := [1, 6, 3, 1, 1, 1, 3, 4]
def baseStart_379853 : Nat := 118140960795 + 379853 * 2 ^ 59
def prefixEnd_379853 : Nat := 4983230072969 + 3 ^ 40 * 379853 * 2
def baseEnd_379853 : Nat := 57791753200713350249065

theorem tailTrace_379853 : CollatzResearch.WordTrace tailWord_379853 prefixEnd_379853 57791753200713350249065 := by
  unfold tailWord_379853
  simp only [CollatzResearch.WordTrace]
  refine ⟨13854377092864929572648213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9236251395243286381765475 13854377092864929572648213)
  ·
    refine ⟨649423926228043573717885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13854377092864929572648213 649423926228043573717885)
    ·
      refine ⟨243533972335516340144207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 649423926228043573717885 243533972335516340144207)
      ·
        refine ⟨365300958503274510216311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243533972335516340144207 365300958503274510216311)
        ·
          refine ⟨547951437754911765324467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365300958503274510216311 547951437754911765324467)
          ·
            refine ⟨821927156632367647986701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547951437754911765324467 821927156632367647986701)
            ·
              refine ⟨308222683737137867995013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 821927156632367647986701 308222683737137867995013)
              ·
                refine ⟨57791753200713350249065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308222683737137867995013 57791753200713350249065)
                ·
                  rfl

theorem cell20_379853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 4].length) (baseStart_379853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379853 prefixEnd_379853 := by exact prefixLift 379853
  have htrace : WordTrace (prefixWord ++ tailWord_379853) baseStart_379853 baseEnd_379853 := by
    simpa [prefixWord, tailWord_379853, baseEnd_379853] using wordTrace_append hprefix tailTrace_379853
  have hstable : (prefixWord ++ tailWord_379853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379853).length < 2 ^ (prefixWord ++ tailWord_379853).sum := by decide
  have hdescent : baseEnd_379853 < baseStart_379853 := by decide
  rcases family_descends (prefixWord ++ tailWord_379853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379854 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_379854 : Nat := 118140960795 + 379854 * 2 ^ 59
def prefixEnd_379854 : Nat := 4983230072969 + 3 ^ 40 * 379854 * 2
def baseEnd_379854 : Nat := 173375716029388491713857

theorem tailTrace_379854 : CollatzResearch.WordTrace tailWord_379854 prefixEnd_379854 173375716029388491713857 := by
  unfold tailWord_379854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731801695732663342929327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9236275710574204495623077 1731801695732663342929327)
  ·
    refine ⟨2597702543598995014393991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1731801695732663342929327 2597702543598995014393991)
    ·
      refine ⟨3896553815398492521590987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2597702543598995014393991 3896553815398492521590987)
      ·
        refine ⟨5844830723097738782386481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3896553815398492521590987 5844830723097738782386481)
        ·
          refine ⟨4383623042323304086789861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5844830723097738782386481 4383623042323304086789861)
          ·
            refine ⟨821929320435619516273099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4383623042323304086789861 821929320435619516273099)
            ·
              refine ⟨1232893980653429274409649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821929320435619516273099 1232893980653429274409649)
              ·
                refine ⟨924670485490071955807237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232893980653429274409649 924670485490071955807237)
                ·
                  refine ⟨173375716029388491713857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924670485490071955807237 173375716029388491713857)
                  ·
                    rfl

theorem cell20_379854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_379854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379854 prefixEnd_379854 := by exact prefixLift 379854
  have htrace : WordTrace (prefixWord ++ tailWord_379854) baseStart_379854 baseEnd_379854 := by
    simpa [prefixWord, tailWord_379854, baseEnd_379854] using wordTrace_append hprefix tailTrace_379854
  have hstable : (prefixWord ++ tailWord_379854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379854).length < 2 ^ (prefixWord ++ tailWord_379854).sum := by decide
  have hdescent : baseEnd_379854 < baseStart_379854 := by decide
  rcases family_descends (prefixWord ++ tailWord_379854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379875 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_379875 : Nat := 118140960795 + 379875 * 2 ^ 59
def prefixEnd_379875 : Nat := 4983230072969 + 3 ^ 40 * 379875 * 2
def baseEnd_379875 : Nat := 173385301001605752013771

theorem tailTrace_379875 : CollatzResearch.WordTrace tailWord_379875 prefixEnd_379875 173385301001605752013771 := by
  unfold tailWord_379875
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855179498785227329949079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9236786332523484886632719 13855179498785227329949079)
  ·
    refine ⟨20782769248177840994923619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13855179498785227329949079 20782769248177840994923619)
    ·
      refine ⟨31174153872266761492385429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20782769248177840994923619 31174153872266761492385429)
      ·
        refine ⟨1461288462762504444955567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31174153872266761492385429 1461288462762504444955567)
        ·
          refine ⟨2191932694143756667433351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1461288462762504444955567 2191932694143756667433351)
          ·
            refine ⟨3287899041215635001150027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191932694143756667433351 3287899041215635001150027)
            ·
              refine ⟨4931848561823452501725041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287899041215635001150027 4931848561823452501725041)
              ·
                refine ⟨3698886421367589376293781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4931848561823452501725041 3698886421367589376293781)
                ·
                  refine ⟨173385301001605752013771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3698886421367589376293781 173385301001605752013771)
                  ·
                    rfl

theorem cell20_379875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_379875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379875 prefixEnd_379875 := by exact prefixLift 379875
  have htrace : WordTrace (prefixWord ++ tailWord_379875) baseStart_379875 baseEnd_379875 := by
    simpa [prefixWord, tailWord_379875, baseEnd_379875] using wordTrace_append hprefix tailTrace_379875
  have hstable : (prefixWord ++ tailWord_379875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379875).length < 2 ^ (prefixWord ++ tailWord_379875).sum := by decide
  have hdescent : baseEnd_379875 < baseStart_379875 := by decide
  rcases family_descends (prefixWord ++ tailWord_379875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379916 : List Nat := [2, 2, 1, 2, 3, 4, 2, 4]
def baseStart_379916 : Nat := 118140960795 + 379916 * 2 ^ 59
def prefixEnd_379916 : Nat := 4983230072969 + 3 ^ 40 * 379916 * 2
def baseEnd_379916 : Nat := 57801338172930610548979

theorem tailTrace_379916 : CollatzResearch.WordTrace tailWord_379916 prefixEnd_379916 57801338172930610548979 := by
  unfold tailWord_379916
  simp only [CollatzResearch.WordTrace]
  refine ⟨6928337445818345666095801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9237783261091127554794401 6928337445818345666095801)
  ·
    refine ⟨5196253084363759249571851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6928337445818345666095801 5196253084363759249571851)
    ·
      refine ⟨7794379626545638874357777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5196253084363759249571851 7794379626545638874357777)
      ·
        refine ⟨5845784719909229155768333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7794379626545638874357777 5845784719909229155768333)
        ·
          refine ⟨2192169269965960933413125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5845784719909229155768333 2192169269965960933413125)
          ·
            refine ⟨411031738118617675014961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2192169269965960933413125 411031738118617675014961)
            ·
              refine ⟨308273803588963256261221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411031738118617675014961 308273803588963256261221)
              ·
                refine ⟨57801338172930610548979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308273803588963256261221 57801338172930610548979)
                ·
                  rfl

theorem cell20_379916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_379916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379916 prefixEnd_379916 := by exact prefixLift 379916
  have htrace : WordTrace (prefixWord ++ tailWord_379916) baseStart_379916 baseEnd_379916 := by
    simpa [prefixWord, tailWord_379916, baseEnd_379916] using wordTrace_append hprefix tailTrace_379916
  have hstable : (prefixWord ++ tailWord_379916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379916).length < 2 ^ (prefixWord ++ tailWord_379916).sum := by decide
  have hdescent : baseEnd_379916 < baseStart_379916 := by decide
  rcases family_descends (prefixWord ++ tailWord_379916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379937 : List Nat := [1, 2, 3, 2, 3, 3, 6]
def baseStart_379937 : Nat := 118140960795 + 379937 * 2 ^ 59
def prefixEnd_379937 : Nat := 4983230072969 + 3 ^ 40 * 379937 * 2
def baseEnd_379937 : Nat := 19268177721223232438539

theorem tailTrace_379937 : CollatzResearch.WordTrace tailWord_379937 prefixEnd_379937 19268177721223232438539 := by
  unfold tailWord_379937
  simp only [CollatzResearch.WordTrace]
  refine ⟨13857440824560611918706065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9238293883040407945804043 13857440824560611918706065)
  ·
    refine ⟨10393080618420458939029549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13857440824560611918706065 10393080618420458939029549)
    ·
      refine ⟨3897405231907672102136081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10393080618420458939029549 3897405231907672102136081)
      ·
        refine ⟨2923053923930754076602061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3897405231907672102136081 2923053923930754076602061)
        ·
          refine ⟨1096145221474032778725773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2923053923930754076602061 1096145221474032778725773)
          ·
            refine ⟨411054458052762292022165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1096145221474032778725773 411054458052762292022165)
            ·
              refine ⟨19268177721223232438539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 411054458052762292022165 19268177721223232438539)
              ·
                rfl

theorem cell20_379937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 6].length) (baseStart_379937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379937 prefixEnd_379937 := by exact prefixLift 379937
  have htrace : WordTrace (prefixWord ++ tailWord_379937) baseStart_379937 baseEnd_379937 := by
    simpa [prefixWord, tailWord_379937, baseEnd_379937] using wordTrace_append hprefix tailTrace_379937
  have hstable : (prefixWord ++ tailWord_379937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379937).length < 2 ^ (prefixWord ++ tailWord_379937).sum := by decide
  have hdescent : baseEnd_379937 < baseStart_379937 := by decide
  rcases family_descends (prefixWord ++ tailWord_379937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379943 : List Nat := [1, 1, 7, 1, 1, 2, 3, 2, 2]
def baseStart_379943 : Nat := 118140960795 + 379943 * 2 ^ 59
def prefixEnd_379943 : Nat := 4983230072969 + 3 ^ 40 * 379943 * 2
def baseEnd_379943 : Nat := 173416338054499737746827

theorem tailTrace_379943 : CollatzResearch.WordTrace tailWord_379943 prefixEnd_379943 173416338054499737746827 := by
  unfold tailWord_379943
  simp only [CollatzResearch.WordTrace]
  refine ⟨13857659662538874943424483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9238439775025916628949655 13857659662538874943424483)
  ·
    refine ⟨20786489493808312415136725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13857659662538874943424483 20786489493808312415136725)
    ·
      refine ⟨487183347511132322229767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 20786489493808312415136725 487183347511132322229767)
      ·
        refine ⟨730775021266698483344651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487183347511132322229767 730775021266698483344651)
        ·
          refine ⟨1096162531900047725016977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730775021266698483344651 1096162531900047725016977)
          ·
            refine ⟨822121898925035793762733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1096162531900047725016977 822121898925035793762733)
            ·
              refine ⟨308295712096888422661025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 822121898925035793762733 308295712096888422661025)
              ·
                refine ⟨231221784072666316995769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308295712096888422661025 231221784072666316995769)
                ·
                  refine ⟨173416338054499737746827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231221784072666316995769 173416338054499737746827)
                  ·
                    rfl

theorem cell20_379943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 2].length) (baseStart_379943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379943 prefixEnd_379943 := by exact prefixLift 379943
  have htrace : WordTrace (prefixWord ++ tailWord_379943) baseStart_379943 baseEnd_379943 := by
    simpa [prefixWord, tailWord_379943, baseEnd_379943] using wordTrace_append hprefix tailTrace_379943
  have hstable : (prefixWord ++ tailWord_379943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379943).length < 2 ^ (prefixWord ++ tailWord_379943).sum := by decide
  have hdescent : baseEnd_379943 < baseStart_379943 := by decide
  rcases family_descends (prefixWord ++ tailWord_379943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379947 : List Nat := [1, 1, 1, 1, 2, 1, 9, 2, 2]
def baseStart_379947 : Nat := 118140960795 + 379947 * 2 ^ 59
def prefixEnd_379947 : Nat := 4983230072969 + 3 ^ 40 * 379947 * 2
def baseEnd_379947 : Nat := 173418163763493501613477

theorem tailTrace_379947 : CollatzResearch.WordTrace tailWord_379947 prefixEnd_379947 173418163763493501613477 := by
  unfold tailWord_379947
  simp only [CollatzResearch.WordTrace]
  refine ⟨13857805554524383626570095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9238537036349589084380063 13857805554524383626570095)
  ·
    refine ⟨20786708331786575439855143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13857805554524383626570095 20786708331786575439855143)
    ·
      refine ⟨31180062497679863159782715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20786708331786575439855143 31180062497679863159782715)
      ·
        refine ⟨46770093746519794739674073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31180062497679863159782715 46770093746519794739674073)
        ·
          refine ⟨35077570309889846054755555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46770093746519794739674073 35077570309889846054755555)
          ·
            refine ⟨52616355464834769082133333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35077570309889846054755555 52616355464834769082133333)
            ·
              refine ⟨308298957801766225090625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 52616355464834769082133333 308298957801766225090625)
              ·
                refine ⟨231224218351324668817969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308298957801766225090625 231224218351324668817969)
                ·
                  refine ⟨173418163763493501613477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231224218351324668817969 173418163763493501613477)
                  ·
                    rfl

theorem cell20_379947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 2].length) (baseStart_379947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379947 prefixEnd_379947 := by exact prefixLift 379947
  have htrace : WordTrace (prefixWord ++ tailWord_379947) baseStart_379947 baseEnd_379947 := by
    simpa [prefixWord, tailWord_379947, baseEnd_379947] using wordTrace_append hprefix tailTrace_379947
  have hstable : (prefixWord ++ tailWord_379947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379947).length < 2 ^ (prefixWord ++ tailWord_379947).sum := by decide
  have hdescent : baseEnd_379947 < baseStart_379947 := by decide
  rcases family_descends (prefixWord ++ tailWord_379947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379961 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 3]
def baseStart_379961 : Nat := 118140960795 + 379961 * 2 ^ 59
def prefixEnd_379961 : Nat := 4983230072969 + 3 ^ 40 * 379961 * 2
def baseEnd_379961 : Nat := 173424553744971675146753

theorem tailTrace_379961 : CollatzResearch.WordTrace tailWord_379961 prefixEnd_379961 173424553744971675146753 := by
  unfold tailWord_379961
  simp only [CollatzResearch.WordTrace]
  refine ⟨13858316176473664017579737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9238877450982442678386491 13858316176473664017579737)
  ·
    refine ⟨10393737132355248013184803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13858316176473664017579737 10393737132355248013184803)
    ·
      refine ⟨15590605698532872019777205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10393737132355248013184803 15590605698532872019777205)
      ·
        refine ⟨1461619284237456751854113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15590605698532872019777205 1461619284237456751854113)
        ·
          refine ⟨1096214463178092563890585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1461619284237456751854113 1096214463178092563890585)
          ·
            refine ⟨822160847383569422917939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1096214463178092563890585 822160847383569422917939)
            ·
              refine ⟨1233241271075354134376909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822160847383569422917939 1233241271075354134376909)
              ·
                refine ⟨462465476653257800391341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1233241271075354134376909 462465476653257800391341)
                ·
                  refine ⟨173424553744971675146753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462465476653257800391341 173424553744971675146753)
                  ·
                    rfl

theorem cell20_379961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_379961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379961 prefixEnd_379961 := by exact prefixLift 379961
  have htrace : WordTrace (prefixWord ++ tailWord_379961) baseStart_379961 baseEnd_379961 := by
    simpa [prefixWord, tailWord_379961, baseEnd_379961] using wordTrace_append hprefix tailTrace_379961
  have hstable : (prefixWord ++ tailWord_379961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379961).length < 2 ^ (prefixWord ++ tailWord_379961).sum := by decide
  have hdescent : baseEnd_379961 < baseStart_379961 := by decide
  rcases family_descends (prefixWord ++ tailWord_379961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379998 : List Nat := [4, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_379998 : Nat := 118140960795 + 379998 * 2 ^ 59
def prefixEnd_379998 : Nat := 4983230072969 + 3 ^ 40 * 379998 * 2
def baseEnd_379998 : Nat := 173441441553163990913269

theorem tailTrace_379998 : CollatzResearch.WordTrace tailWord_379998 prefixEnd_379998 173441441553163990913269 := by
  unfold tailWord_379998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1732458209667452417084581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9239777118226412891117765 1732458209667452417084581)
  ·
    refine ⟨324835914312647328203359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1732458209667452417084581 324835914312647328203359)
    ·
      refine ⟨487253871468970992305039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324835914312647328203359 487253871468970992305039)
      ·
        refine ⟨730880807203456488457559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487253871468970992305039 730880807203456488457559)
        ·
          refine ⟨1096321210805184732686339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730880807203456488457559 1096321210805184732686339)
          ·
            refine ⟨1644481816207777099029509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096321210805184732686339 1644481816207777099029509)
            ·
              refine ⟨308340340538958206068033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1644481816207777099029509 308340340538958206068033)
              ·
                refine ⟨231255255404218654551025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308340340538958206068033 231255255404218654551025)
                ·
                  refine ⟨173441441553163990913269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231255255404218654551025 173441441553163990913269)
                  ·
                    rfl

theorem cell20_379998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_379998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_379998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_379998 prefixEnd_379998 := by exact prefixLift 379998
  have htrace : WordTrace (prefixWord ++ tailWord_379998) baseStart_379998 baseEnd_379998 := by
    simpa [prefixWord, tailWord_379998, baseEnd_379998] using wordTrace_append hprefix tailTrace_379998
  have hstable : (prefixWord ++ tailWord_379998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379998).length < 2 ^ (prefixWord ++ tailWord_379998).sum := by decide
  have hdescent : baseEnd_379998 < baseStart_379998 := by decide
  rcases family_descends (prefixWord ++ tailWord_379998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380002 : List Nat := [3, 3, 2, 2, 1, 2, 1, 4, 2]
def baseStart_380002 : Nat := 118140960795 + 380002 * 2 ^ 59
def prefixEnd_380002 : Nat := 4983230072969 + 3 ^ 40 * 380002 * 2
def baseEnd_380002 : Nat := 173443267262157754779919

theorem tailTrace_380002 : CollatzResearch.WordTrace tailWord_380002 prefixEnd_380002 173443267262157754779919 := by
  unfold tailWord_380002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464952892331282004955565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9239874379550085346548173 3464952892331282004955565)
  ·
    refine ⟨1299357334624230751858337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3464952892331282004955565 1299357334624230751858337)
    ·
      refine ⟨974518000968173063893753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1299357334624230751858337 974518000968173063893753)
      ·
        refine ⟨730888500726129797920315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 974518000968173063893753 730888500726129797920315)
        ·
          refine ⟨1096332751089194696880473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730888500726129797920315 1096332751089194696880473)
          ·
            refine ⟨822249563316896022660355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1096332751089194696880473 822249563316896022660355)
            ·
              refine ⟨1233374344975344033990533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822249563316896022660355 1233374344975344033990533)
              ·
                refine ⟨231257689682877006373225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1233374344975344033990533 231257689682877006373225)
                ·
                  refine ⟨173443267262157754779919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231257689682877006373225 173443267262157754779919)
                  ·
                    rfl

theorem cell20_380002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_380002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380002 prefixEnd_380002 := by exact prefixLift 380002
  have htrace : WordTrace (prefixWord ++ tailWord_380002) baseStart_380002 baseEnd_380002 := by
    simpa [prefixWord, tailWord_380002, baseEnd_380002] using wordTrace_append hprefix tailTrace_380002
  have hstable : (prefixWord ++ tailWord_380002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380002).length < 2 ^ (prefixWord ++ tailWord_380002).sum := by decide
  have hdescent : baseEnd_380002 < baseStart_380002 := by decide
  rcases family_descends (prefixWord ++ tailWord_380002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380013 : List Nat := [1, 5, 1, 1, 2, 2, 3, 5]
def baseStart_380013 : Nat := 118140960795 + 380013 * 2 ^ 59
def prefixEnd_380013 : Nat := 4983230072969 + 3 ^ 40 * 380013 * 2
def baseEnd_380013 : Nat := 57816095987296868471069

theorem tailTrace_380013 : CollatzResearch.WordTrace tailWord_380013 prefixEnd_380013 57816095987296868471069 := by
  unfold tailWord_380013
  simp only [CollatzResearch.WordTrace]
  refine ⟨13860212772285276898472693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9240141848190184598981795 13860212772285276898472693)
  ·
    refine ⟨1299394947401744709231815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13860212772285276898472693 1299394947401744709231815)
    ·
      refine ⟨1949092421102617063847723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299394947401744709231815 1949092421102617063847723)
      ·
        refine ⟨2923638631653925595771585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1949092421102617063847723 2923638631653925595771585)
        ·
          refine ⟨2192728973740444196828689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2923638631653925595771585 2192728973740444196828689)
          ·
            refine ⟨1644546730305333147621517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2192728973740444196828689 1644546730305333147621517)
            ·
              refine ⟨616705023864499930358069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1644546730305333147621517 616705023864499930358069)
              ·
                refine ⟨57816095987296868471069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 616705023864499930358069 57816095987296868471069)
                ·
                  rfl

theorem cell20_380013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_380013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380013 prefixEnd_380013 := by exact prefixLift 380013
  have htrace : WordTrace (prefixWord ++ tailWord_380013) baseStart_380013 baseEnd_380013 := by
    simpa [prefixWord, tailWord_380013, baseEnd_380013] using wordTrace_append hprefix tailTrace_380013
  have hstable : (prefixWord ++ tailWord_380013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380013).length < 2 ^ (prefixWord ++ tailWord_380013).sum := by decide
  have hdescent : baseEnd_380013 < baseStart_380013 := by decide
  rcases family_descends (prefixWord ++ tailWord_380013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380040 : List Nat := [2, 1, 3, 4, 2, 1, 2, 3, 2]
def baseStart_380040 : Nat := 118140960795 + 380040 * 2 ^ 59
def prefixEnd_380040 : Nat := 4983230072969 + 3 ^ 40 * 380040 * 2
def baseEnd_380040 : Nat := 173460611497598511513097

theorem tailTrace_380040 : CollatzResearch.WordTrace tailWord_380040 prefixEnd_380040 173460611497598511513097 := by
  unfold tailWord_380040
  simp only [CollatzResearch.WordTrace]
  refine ⟨6930598771593730254852787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9240798362124973673137049 6930598771593730254852787)
  ·
    refine ⟨10395898157390595382279181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6930598771593730254852787 10395898157390595382279181)
    ·
      refine ⟨3898461809021473268354693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10395898157390595382279181 3898461809021473268354693)
      ·
        refine ⟨730961589191526237816505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3898461809021473268354693 730961589191526237816505)
        ·
          refine ⟨548221191893644678362379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730961589191526237816505 548221191893644678362379)
          ·
            refine ⟨822331787840467017543569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548221191893644678362379 822331787840467017543569)
            ·
              refine ⟨616748840880350263157677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822331787840467017543569 616748840880350263157677)
              ·
                refine ⟨231280815330131348684129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 616748840880350263157677 231280815330131348684129)
                ·
                  refine ⟨173460611497598511513097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231280815330131348684129 173460611497598511513097)
                  ·
                    rfl

theorem cell20_380040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_380040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380040 prefixEnd_380040 := by exact prefixLift 380040
  have htrace : WordTrace (prefixWord ++ tailWord_380040) baseStart_380040 baseEnd_380040 := by
    simpa [prefixWord, tailWord_380040, baseEnd_380040] using wordTrace_append hprefix tailTrace_380040
  have hstable : (prefixWord ++ tailWord_380040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380040).length < 2 ^ (prefixWord ++ tailWord_380040).sum := by decide
  have hdescent : baseEnd_380040 < baseStart_380040 := by decide
  rcases family_descends (prefixWord ++ tailWord_380040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380089 : List Nat := [1, 2, 1, 4, 1, 3, 4, 4]
def baseStart_380089 : Nat := 118140960795 + 380089 * 2 ^ 59
def prefixEnd_380089 : Nat := 4983230072969 + 3 ^ 40 * 380089 * 2
def baseEnd_380089 : Nat := 57827658810924039626521

theorem tailTrace_380089 : CollatzResearch.WordTrace tailWord_380089 prefixEnd_380089 57827658810924039626521 := by
  unfold tailWord_380089
  simp only [CollatzResearch.WordTrace]
  refine ⟨13862984720009941878239321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9241989813339961252159547 13862984720009941878239321)
  ·
    refine ⟨10397238540007456408679491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13862984720009941878239321 10397238540007456408679491)
    ·
      refine ⟨15595857810011184613019237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10397238540007456408679491 15595857810011184613019237)
      ·
        refine ⟨2924223339377097114941107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15595857810011184613019237 2924223339377097114941107)
        ·
          refine ⟨4386335009065645672411661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924223339377097114941107 4386335009065645672411661)
          ·
            refine ⟨1644875628399617127154373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4386335009065645672411661 1644875628399617127154373)
            ·
              refine ⟨308414180324928211341445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1644875628399617127154373 308414180324928211341445)
              ·
                refine ⟨57827658810924039626521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308414180324928211341445 57827658810924039626521)
                ·
                  rfl

theorem cell20_380089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 4].length) (baseStart_380089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380089 prefixEnd_380089 := by exact prefixLift 380089
  have htrace : WordTrace (prefixWord ++ tailWord_380089) baseStart_380089 baseEnd_380089 := by
    simpa [prefixWord, tailWord_380089, baseEnd_380089] using wordTrace_append hprefix tailTrace_380089
  have hstable : (prefixWord ++ tailWord_380089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380089).length < 2 ^ (prefixWord ++ tailWord_380089).sum := by decide
  have hdescent : baseEnd_380089 < baseStart_380089 := by decide
  rcases family_descends (prefixWord ++ tailWord_380089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380102 : List Nat := [6, 1, 2, 2, 1, 2, 6]
def baseStart_380102 : Nat := 118140960795 + 380102 * 2 ^ 59
def prefixEnd_380102 : Nat := 4983230072969 + 3 ^ 40 * 380102 * 2
def baseEnd_380102 : Nat := 19276545554111316827353

theorem tailTrace_380102 : CollatzResearch.WordTrace tailWord_380102 prefixEnd_380102 19276545554111316827353 := by
  unfold tailWord_380102
  simp only [CollatzResearch.WordTrace]
  refine ⟨433233089655088909326955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9242305912641896732308373 433233089655088909326955)
  ·
    refine ⟨649849634482633363990433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 433233089655088909326955 649849634482633363990433)
    ·
      refine ⟨487387225861975022992825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 649849634482633363990433 487387225861975022992825)
      ·
        refine ⟨365540419396481267244619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487387225861975022992825 365540419396481267244619)
        ·
          refine ⟨548310629094721900866929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365540419396481267244619 548310629094721900866929)
          ·
            refine ⟨411232971821041425650197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548310629094721900866929 411232971821041425650197)
            ·
              refine ⟨19276545554111316827353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 411232971821041425650197 19276545554111316827353)
              ·
                rfl

theorem cell20_380102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 6].length) (baseStart_380102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380102 prefixEnd_380102 := by exact prefixLift 380102
  have htrace : WordTrace (prefixWord ++ tailWord_380102) baseStart_380102 baseEnd_380102 := by
    simpa [prefixWord, tailWord_380102, baseEnd_380102] using wordTrace_append hprefix tailTrace_380102
  have hstable : (prefixWord ++ tailWord_380102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380102).length < 2 ^ (prefixWord ++ tailWord_380102).sum := by decide
  have hdescent : baseEnd_380102 < baseStart_380102 := by decide
  rcases family_descends (prefixWord ++ tailWord_380102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380116 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 4]
def baseStart_380116 : Nat := 118140960795 + 380116 * 2 ^ 59
def prefixEnd_380116 : Nat := 4983230072969 + 3 ^ 40 * 380116 * 2
def baseEnd_380116 : Nat := 173495299968480024979453

theorem tailTrace_380116 : CollatzResearch.WordTrace tailWord_380116 prefixEnd_380116 173495299968480024979453 := by
  unfold tailWord_380116
  simp only [CollatzResearch.WordTrace]
  refine ⟨6931984745456062744736101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9242646327274750326314801 6931984745456062744736101)
  ·
    refine ⟨1299747139773011764638019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6931984745456062744736101 1299747139773011764638019)
    ·
      refine ⟨1949620709659517646957029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299747139773011764638019 1949620709659517646957029)
      ·
        refine ⟨365553883061159558804443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1949620709659517646957029 365553883061159558804443)
        ·
          refine ⟨548330824591739338206665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365553883061159558804443 548330824591739338206665)
          ·
            refine ⟨411248118443804503654999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548330824591739338206665 411248118443804503654999)
            ·
              refine ⟨616872177665706755482499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411248118443804503654999 616872177665706755482499)
              ·
                refine ⟨925308266498560133223749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616872177665706755482499 925308266498560133223749)
                ·
                  refine ⟨173495299968480024979453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925308266498560133223749 173495299968480024979453)
                  ·
                    rfl

theorem cell20_380116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_380116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380116 prefixEnd_380116 := by exact prefixLift 380116
  have htrace : WordTrace (prefixWord ++ tailWord_380116) baseStart_380116 baseEnd_380116 := by
    simpa [prefixWord, tailWord_380116, baseEnd_380116] using wordTrace_append hprefix tailTrace_380116
  have hstable : (prefixWord ++ tailWord_380116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380116).length < 2 ^ (prefixWord ++ tailWord_380116).sum := by decide
  have hdescent : baseEnd_380116 < baseStart_380116 := by decide
  rcases family_descends (prefixWord ++ tailWord_380116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380172 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 3]
def baseStart_380172 : Nat := 118140960795 + 380172 * 2 ^ 59
def prefixEnd_380172 : Nat := 4983230072969 + 3 ^ 40 * 380172 * 2
def baseEnd_380172 : Nat := 173520859894392719112557

theorem tailTrace_380172 : CollatzResearch.WordTrace tailWord_380172 prefixEnd_380172 173520859894392719112557 := by
  unfold tailWord_380172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6933005989354623526755385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9244007985806164702340513 6933005989354623526755385)
  ·
    refine ⟨5199754492015967645066539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6933005989354623526755385 5199754492015967645066539)
    ·
      refine ⟨7799631738023951467599809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5199754492015967645066539 7799631738023951467599809)
      ·
        refine ⟨5849723803517963600699857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7799631738023951467599809 5849723803517963600699857)
        ·
          refine ⟨4387292852638472700524893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5849723803517963600699857 4387292852638472700524893)
          ·
            refine ⟨1645234819739427262696835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4387292852638472700524893 1645234819739427262696835)
            ·
              refine ⟨2467852229609140894045253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645234819739427262696835 2467852229609140894045253)
              ·
                refine ⟨462722293051713917633485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2467852229609140894045253 462722293051713917633485)
                ·
                  refine ⟨173520859894392719112557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462722293051713917633485 173520859894392719112557)
                  ·
                    rfl

theorem cell20_380172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_380172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380172 prefixEnd_380172 := by exact prefixLift 380172
  have htrace : WordTrace (prefixWord ++ tailWord_380172) baseStart_380172 baseEnd_380172 := by
    simpa [prefixWord, tailWord_380172, baseEnd_380172] using wordTrace_append hprefix tailTrace_380172
  have hstable : (prefixWord ++ tailWord_380172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380172).length < 2 ^ (prefixWord ++ tailWord_380172).sum := by decide
  have hdescent : baseEnd_380172 < baseStart_380172 := by decide
  rcases family_descends (prefixWord ++ tailWord_380172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380178 : List Nat := [3, 2, 4, 2, 2, 1, 1, 5]
def baseStart_380178 : Nat := 118140960795 + 380178 * 2 ^ 59
def prefixEnd_380178 : Nat := 4983230072969 + 3 ^ 40 * 380178 * 2
def baseEnd_380178 : Nat := 57841199485961121637511

theorem tailTrace_380178 : CollatzResearch.WordTrace tailWord_380178 prefixEnd_380178 57841199485961121637511 := by
  unfold tailWord_380178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3466557704171877519557297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9244153877791673385486125 3466557704171877519557297)
  ·
    refine ⟨2599918278128908139667973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3466557704171877519557297 2599918278128908139667973)
    ·
      refine ⟨487484677149170276187745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2599918278128908139667973 487484677149170276187745)
      ·
        refine ⟨365613507861877707140809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487484677149170276187745 365613507861877707140809)
        ·
          refine ⟨274210130896408280355607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365613507861877707140809 274210130896408280355607)
          ·
            refine ⟨411315196344612420533411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274210130896408280355607 411315196344612420533411)
            ·
              refine ⟨616972794516918630800117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411315196344612420533411 616972794516918630800117)
              ·
                refine ⟨57841199485961121637511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 616972794516918630800117 57841199485961121637511)
                ·
                  rfl

theorem cell20_380178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_380178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380178 prefixEnd_380178 := by exact prefixLift 380178
  have htrace : WordTrace (prefixWord ++ tailWord_380178) baseStart_380178 baseEnd_380178 := by
    simpa [prefixWord, tailWord_380178, baseEnd_380178] using wordTrace_append hprefix tailTrace_380178
  have hstable : (prefixWord ++ tailWord_380178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380178).length < 2 ^ (prefixWord ++ tailWord_380178).sum := by decide
  have hdescent : baseEnd_380178 < baseStart_380178 := by decide
  rcases family_descends (prefixWord ++ tailWord_380178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380189 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 3]
def baseStart_380189 : Nat := 118140960795 + 380189 * 2 ^ 59
def prefixEnd_380189 : Nat := 4983230072969 + 3 ^ 40 * 380189 * 2
def baseEnd_380189 : Nat := 173528619157616215545821

theorem tailTrace_380189 : CollatzResearch.WordTrace tailWord_380189 prefixEnd_380189 173528619157616215545821 := by
  unfold tailWord_380189
  simp only [CollatzResearch.WordTrace]
  refine ⟨13866632019647658956879621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9244421346431772637919747 13866632019647658956879621)
  ·
    refine ⟨2599993503683936054414929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13866632019647658956879621 2599993503683936054414929)
    ·
      refine ⟨1949995127762952040811197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2599993503683936054414929 1949995127762952040811197)
      ·
        refine ⟨731248172911107015304199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1949995127762952040811197 731248172911107015304199)
        ·
          refine ⟨1096872259366660522956299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731248172911107015304199 1096872259366660522956299)
          ·
            refine ⟨1645308389049990784434449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096872259366660522956299 1645308389049990784434449)
            ·
              refine ⟨1233981291787493088325837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1645308389049990784434449 1233981291787493088325837)
              ·
                refine ⟨462742984420309908122189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1233981291787493088325837 462742984420309908122189)
                ·
                  refine ⟨173528619157616215545821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462742984420309908122189 173528619157616215545821)
                  ·
                    rfl

theorem cell20_380189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_380189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380189 prefixEnd_380189 := by exact prefixLift 380189
  have htrace : WordTrace (prefixWord ++ tailWord_380189) baseStart_380189 baseEnd_380189 := by
    simpa [prefixWord, tailWord_380189, baseEnd_380189] using wordTrace_append hprefix tailTrace_380189
  have hstable : (prefixWord ++ tailWord_380189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380189).length < 2 ^ (prefixWord ++ tailWord_380189).sum := by decide
  have hdescent : baseEnd_380189 < baseStart_380189 := by decide
  rcases family_descends (prefixWord ++ tailWord_380189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380193 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_380193 : Nat := 118140960795 + 380193 * 2 ^ 59
def prefixEnd_380193 : Nat := 4983230072969 + 3 ^ 40 * 380193 * 2
def baseEnd_380193 : Nat := 173530444866609979412471

theorem tailTrace_380193 : CollatzResearch.WordTrace tailWord_380193 prefixEnd_380193 173530444866609979412471 := by
  unfold tailWord_380193
  simp only [CollatzResearch.WordTrace]
  refine ⟨13866777911633167640025233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9244518607755445093350155 13866777911633167640025233)
  ·
    refine ⟨10400083433724875730018925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13866777911633167640025233 10400083433724875730018925)
    ·
      refine ⟨3900031287646828398757097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10400083433724875730018925 3900031287646828398757097)
      ·
        refine ⟨2925023465735121299067823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3900031287646828398757097 2925023465735121299067823)
        ·
          refine ⟨4387535198602681948601735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925023465735121299067823 4387535198602681948601735)
          ·
            refine ⟨6581302797904022922902603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387535198602681948601735 6581302797904022922902603)
            ·
              refine ⟨9871954196856034384353905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6581302797904022922902603 9871954196856034384353905)
              ·
                refine ⟨7403965647642025788265429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9871954196856034384353905 7403965647642025788265429)
                ·
                  refine ⟨173530444866609979412471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7403965647642025788265429 173530444866609979412471)
                  ·
                    rfl

theorem cell20_380193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_380193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380193 prefixEnd_380193 := by exact prefixLift 380193
  have htrace : WordTrace (prefixWord ++ tailWord_380193) baseStart_380193 baseEnd_380193 := by
    simpa [prefixWord, tailWord_380193, baseEnd_380193] using wordTrace_append hprefix tailTrace_380193
  have hstable : (prefixWord ++ tailWord_380193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380193).length < 2 ^ (prefixWord ++ tailWord_380193).sum := by decide
  have hdescent : baseEnd_380193 < baseStart_380193 := by decide
  rcases family_descends (prefixWord ++ tailWord_380193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380213 : List Nat := [1, 3, 3, 1, 2, 3, 2, 3, 2]
def baseStart_380213 : Nat := 118140960795 + 380213 * 2 ^ 59
def prefixEnd_380213 : Nat := 4983230072969 + 3 ^ 40 * 380213 * 2
def baseEnd_380213 : Nat := 173539573411578798745723

theorem tailTrace_380213 : CollatzResearch.WordTrace tailWord_380213 prefixEnd_380213 173539573411578798745723 := by
  unfold tailWord_380213
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867507371560711055753293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9245004914373807370502195 13867507371560711055753293)
  ·
    refine ⟨5200315264335266645907485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13867507371560711055753293 5200315264335266645907485)
    ·
      refine ⟨1950118224125724992215307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5200315264335266645907485 1950118224125724992215307)
      ·
        refine ⟨2925177336188587488322961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950118224125724992215307 2925177336188587488322961)
        ·
          refine ⟨2193883002141440616242221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2925177336188587488322961 2193883002141440616242221)
          ·
            refine ⟨822706125803040231090833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2193883002141440616242221 822706125803040231090833)
            ·
              refine ⟨617029594352280173318125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822706125803040231090833 617029594352280173318125)
              ·
                refine ⟨231386097882105064994297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617029594352280173318125 231386097882105064994297)
                ·
                  refine ⟨173539573411578798745723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231386097882105064994297 173539573411578798745723)
                  ·
                    rfl

theorem cell20_380213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_380213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380213 prefixEnd_380213 := by exact prefixLift 380213
  have htrace : WordTrace (prefixWord ++ tailWord_380213) baseStart_380213 baseEnd_380213 := by
    simpa [prefixWord, tailWord_380213, baseEnd_380213] using wordTrace_append hprefix tailTrace_380213
  have hstable : (prefixWord ++ tailWord_380213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380213).length < 2 ^ (prefixWord ++ tailWord_380213).sum := by decide
  have hdescent : baseEnd_380213 < baseStart_380213 := by decide
  rcases family_descends (prefixWord ++ tailWord_380213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380289 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 4]
def baseStart_380289 : Nat := 118140960795 + 380289 * 2 ^ 59
def prefixEnd_380289 : Nat := 4983230072969 + 3 ^ 40 * 380289 * 2
def baseEnd_380289 : Nat := 173574261882460312212079

theorem tailTrace_380289 : CollatzResearch.WordTrace tailWord_380289 prefixEnd_380289 173574261882460312212079 := by
  unfold tailWord_380289
  simp only [CollatzResearch.WordTrace]
  refine ⟨13870279319285376035519921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9246852879523584023679947 13870279319285376035519921)
  ·
    refine ⟨10402709489464032026639941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13870279319285376035519921 10402709489464032026639941)
    ·
      refine ⟨1950508029274506004994989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10402709489464032026639941 1950508029274506004994989)
      ·
        refine ⟨731440510977939751873121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1950508029274506004994989 731440510977939751873121)
        ·
          refine ⟨548580383233454813904841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731440510977939751873121 548580383233454813904841)
          ·
            refine ⟨411435287425091110428631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548580383233454813904841 411435287425091110428631)
            ·
              refine ⟨617152931137636665642947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411435287425091110428631 617152931137636665642947)
              ·
                refine ⟨925729396706454998464421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617152931137636665642947 925729396706454998464421)
                ·
                  refine ⟨173574261882460312212079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925729396706454998464421 173574261882460312212079)
                  ·
                    rfl

theorem cell20_380289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_380289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380289 prefixEnd_380289 := by exact prefixLift 380289
  have htrace : WordTrace (prefixWord ++ tailWord_380289) baseStart_380289 baseEnd_380289 := by
    simpa [prefixWord, tailWord_380289, baseEnd_380289] using wordTrace_append hprefix tailTrace_380289
  have hstable : (prefixWord ++ tailWord_380289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380289).length < 2 ^ (prefixWord ++ tailWord_380289).sum := by decide
  have hdescent : baseEnd_380289 < baseStart_380289 := by decide
  rcases family_descends (prefixWord ++ tailWord_380289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380293 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 4]
def baseStart_380293 : Nat := 118140960795 + 380293 * 2 ^ 59
def prefixEnd_380293 : Nat := 4983230072969 + 3 ^ 40 * 380293 * 2
def baseEnd_380293 : Nat := 173576087591454076078729

theorem tailTrace_380293 : CollatzResearch.WordTrace tailWord_380293 prefixEnd_380293 173576087591454076078729 := by
  unfold tailWord_380293
  simp only [CollatzResearch.WordTrace]
  refine ⟨13870425211270884718665533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9246950140847256479110355 13870425211270884718665533)
  ·
    refine ⟨5201409454226581769499575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13870425211270884718665533 5201409454226581769499575)
    ·
      refine ⟨7802114181339872654249363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5201409454226581769499575 7802114181339872654249363)
      ·
        refine ⟨11703171272009808981374045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7802114181339872654249363 11703171272009808981374045)
        ·
          refine ⟨4388689227003678368015267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11703171272009808981374045 4388689227003678368015267)
          ·
            refine ⟨6583033840505517552022901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388689227003678368015267 6583033840505517552022901)
            ·
              refine ⟨617159422547392270502147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6583033840505517552022901 617159422547392270502147)
              ·
                refine ⟨925739133821088405753221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617159422547392270502147 925739133821088405753221)
                ·
                  refine ⟨173576087591454076078729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925739133821088405753221 173576087591454076078729)
                  ·
                    rfl

theorem cell20_380293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_380293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380293 prefixEnd_380293 := by exact prefixLift 380293
  have htrace : WordTrace (prefixWord ++ tailWord_380293) baseStart_380293 baseEnd_380293 := by
    simpa [prefixWord, tailWord_380293, baseEnd_380293] using wordTrace_append hprefix tailTrace_380293
  have hstable : (prefixWord ++ tailWord_380293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380293).length < 2 ^ (prefixWord ++ tailWord_380293).sum := by decide
  have hdescent : baseEnd_380293 < baseStart_380293 := by decide
  rcases family_descends (prefixWord ++ tailWord_380293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380300 : List Nat := [2, 2, 1, 2, 1, 3, 4, 5]
def baseStart_380300 : Nat := 118140960795 + 380300 * 2 ^ 59
def prefixEnd_380300 : Nat := 4983230072969 + 3 ^ 40 * 380300 * 2
def baseEnd_380300 : Nat := 57859760860731054281789

theorem tailTrace_380300 : CollatzResearch.WordTrace tailWord_380300 prefixEnd_380300 57859760860731054281789 := by
  unfold tailWord_380300
  simp only [CollatzResearch.WordTrace]
  refine ⟨6935340261122762457085177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9247120348163683276113569 6935340261122762457085177)
  ·
    refine ⟨5201505195842071842813883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6935340261122762457085177 5201505195842071842813883)
    ·
      refine ⟨7802257793763107764220825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5201505195842071842813883 7802257793763107764220825)
      ·
        refine ⟨5851693345322330823165619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7802257793763107764220825 5851693345322330823165619)
        ·
          refine ⟨8777540017983496234748429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851693345322330823165619 8777540017983496234748429)
          ·
            refine ⟨3291577506743811088030661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8777540017983496234748429 3291577506743811088030661)
            ·
              refine ⟨617170782514464579005749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3291577506743811088030661 617170782514464579005749)
              ·
                refine ⟨57859760860731054281789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 617170782514464579005749 57859760860731054281789)
                ·
                  rfl

theorem cell20_380300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_380300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380300 prefixEnd_380300 := by exact prefixLift 380300
  have htrace : WordTrace (prefixWord ++ tailWord_380300) baseStart_380300 baseEnd_380300 := by
    simpa [prefixWord, tailWord_380300, baseEnd_380300] using wordTrace_append hprefix tailTrace_380300
  have hstable : (prefixWord ++ tailWord_380300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380300).length < 2 ^ (prefixWord ++ tailWord_380300).sum := by decide
  have hdescent : baseEnd_380300 < baseStart_380300 := by decide
  rcases family_descends (prefixWord ++ tailWord_380300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380341 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 3]
def baseStart_380341 : Nat := 118140960795 + 380341 * 2 ^ 59
def prefixEnd_380341 : Nat := 4983230072969 + 3 ^ 40 * 380341 * 2
def baseEnd_380341 : Nat := 173597996099379242478533

theorem tailTrace_380341 : CollatzResearch.WordTrace tailWord_380341 prefixEnd_380341 173597996099379242478533 := by
  unfold tailWord_380341
  simp only [CollatzResearch.WordTrace]
  refine ⟨13872175915096988916412877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9248117276731325944275251 13872175915096988916412877)
  ·
    refine ⟨5202065968161370843654829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13872175915096988916412877 5202065968161370843654829)
    ·
      refine ⟨1950774738060514066370561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5202065968161370843654829 1950774738060514066370561)
      ·
        refine ⟨1463081053545385549777921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1950774738060514066370561 1463081053545385549777921)
        ·
          refine ⟨1097310790159039162333441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1463081053545385549777921 1097310790159039162333441)
          ·
            refine ⟨822983092619279371750081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1097310790159039162333441 822983092619279371750081)
            ·
              refine ⟨617237319464459528812561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822983092619279371750081 617237319464459528812561)
              ·
                refine ⟨462927989598344646609421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617237319464459528812561 462927989598344646609421)
                ·
                  refine ⟨173597996099379242478533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462927989598344646609421 173597996099379242478533)
                  ·
                    rfl

theorem cell20_380341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_380341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380341 prefixEnd_380341 := by exact prefixLift 380341
  have htrace : WordTrace (prefixWord ++ tailWord_380341) baseStart_380341 baseEnd_380341 := by
    simpa [prefixWord, tailWord_380341, baseEnd_380341] using wordTrace_append hprefix tailTrace_380341
  have hstable : (prefixWord ++ tailWord_380341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380341).length < 2 ^ (prefixWord ++ tailWord_380341).sum := by decide
  have hdescent : baseEnd_380341 < baseStart_380341 := by decide
  rcases family_descends (prefixWord ++ tailWord_380341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380362 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_380362 : Nat := 118140960795 + 380362 * 2 ^ 59
def prefixEnd_380362 : Nat := 4983230072969 + 3 ^ 40 * 380362 * 2
def baseEnd_380362 : Nat := 173607581071596502778447

theorem tailTrace_380362 : CollatzResearch.WordTrace tailWord_380362 prefixEnd_380362 173607581071596502778447 := by
  unfold tailWord_380362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3468235462005227375731835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9248627898680606335284893 3468235462005227375731835)
  ·
    refine ⟨5202353193007841063597753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3468235462005227375731835 5202353193007841063597753)
    ·
      refine ⟨3901764894755880797698315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5202353193007841063597753 3901764894755880797698315)
      ·
        refine ⟨5852647342133821196547473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3901764894755880797698315 5852647342133821196547473)
        ·
          refine ⟨4389485506600365897410605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5852647342133821196547473 4389485506600365897410605)
          ·
            refine ⟨1646057064975137211528977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4389485506600365897410605 1646057064975137211528977)
            ·
              refine ⟨1234542798731352908646733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646057064975137211528977 1234542798731352908646733)
              ·
                refine ⟨462953549524257340742525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1234542798731352908646733 462953549524257340742525)
                ·
                  refine ⟨173607581071596502778447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462953549524257340742525 173607581071596502778447)
                  ·
                    rfl

theorem cell20_380362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_380362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380362 prefixEnd_380362 := by exact prefixLift 380362
  have htrace : WordTrace (prefixWord ++ tailWord_380362) baseStart_380362 baseEnd_380362 := by
    simpa [prefixWord, tailWord_380362, baseEnd_380362] using wordTrace_append hprefix tailTrace_380362
  have hstable : (prefixWord ++ tailWord_380362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380362).length < 2 ^ (prefixWord ++ tailWord_380362).sum := by decide
  have hdescent : baseEnd_380362 < baseStart_380362 := by decide
  rcases family_descends (prefixWord ++ tailWord_380362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380372 : List Nat := [2, 4, 1, 2, 3, 1, 3, 4]
def baseStart_380372 : Nat := 118140960795 + 380372 * 2 ^ 59
def prefixEnd_380372 : Nat := 4983230072969 + 3 ^ 40 * 380372 * 2
def baseEnd_380372 : Nat := 57870715114693637481691

theorem tailTrace_380372 : CollatzResearch.WordTrace tailWord_380372 prefixEnd_380372 57870715114693637481691 := by
  unfold tailWord_380372
  simp only [CollatzResearch.WordTrace]
  refine ⟨6936653288992340605395685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9248871051989787473860913 6936653288992340605395685)
  ·
    refine ⟨1300622491686063863511691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6936653288992340605395685 1300622491686063863511691)
    ·
      refine ⟨1950933737529095795267537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1300622491686063863511691 1950933737529095795267537)
      ·
        refine ⟨1463200303146821846450653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1950933737529095795267537 1463200303146821846450653)
        ·
          refine ⟨548700113680058192418995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1463200303146821846450653 548700113680058192418995)
          ·
            refine ⟨823050170520087288628493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548700113680058192418995 823050170520087288628493)
            ·
              refine ⟨308643813945032733235685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 823050170520087288628493 308643813945032733235685)
              ·
                refine ⟨57870715114693637481691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308643813945032733235685 57870715114693637481691)
                ·
                  rfl

theorem cell20_380372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_380372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380372 prefixEnd_380372 := by exact prefixLift 380372
  have htrace : WordTrace (prefixWord ++ tailWord_380372) baseStart_380372 baseEnd_380372 := by
    simpa [prefixWord, tailWord_380372, baseEnd_380372] using wordTrace_append hprefix tailTrace_380372
  have hstable : (prefixWord ++ tailWord_380372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380372).length < 2 ^ (prefixWord ++ tailWord_380372).sum := by decide
  have hdescent : baseEnd_380372 < baseStart_380372 := by decide
  rcases family_descends (prefixWord ++ tailWord_380372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380383 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_380383 : Nat := 118140960795 + 380383 * 2 ^ 59
def prefixEnd_380383 : Nat := 4983230072969 + 3 ^ 40 * 380383 * 2
def baseEnd_380383 : Nat := 173617166043813763078361

theorem tailTrace_380383 : CollatzResearch.WordTrace tailWord_380383 prefixEnd_380383 173617166043813763078361 := by
  unfold tailWord_380383
  simp only [CollatzResearch.WordTrace]
  refine ⟨13873707780944830089441803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9249138520629886726294535 13873707780944830089441803)
  ·
    refine ⟨20810561671417245134162705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13873707780944830089441803 20810561671417245134162705)
    ·
      refine ⟨15607921253562933850622029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20810561671417245134162705 15607921253562933850622029)
      ·
        refine ⟨5852970470086100193983261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15607921253562933850622029 5852970470086100193983261)
        ·
          refine ⟨2194863926282287572743723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5852970470086100193983261 2194863926282287572743723)
          ·
            refine ⟨3292295889423431359115585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194863926282287572743723 3292295889423431359115585)
            ·
              refine ⟨2469221917067573519336689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3292295889423431359115585 2469221917067573519336689)
              ·
                refine ⟨1851916437800680139502517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469221917067573519336689 1851916437800680139502517)
                ·
                  refine ⟨173617166043813763078361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1851916437800680139502517 173617166043813763078361)
                  ·
                    rfl

theorem cell20_380383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_380383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380383 prefixEnd_380383 := by exact prefixLift 380383
  have htrace : WordTrace (prefixWord ++ tailWord_380383) baseStart_380383 baseEnd_380383 := by
    simpa [prefixWord, tailWord_380383, baseEnd_380383] using wordTrace_append hprefix tailTrace_380383
  have hstable : (prefixWord ++ tailWord_380383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380383).length < 2 ^ (prefixWord ++ tailWord_380383).sum := by decide
  have hdescent : baseEnd_380383 < baseStart_380383 := by decide
  rcases family_descends (prefixWord ++ tailWord_380383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380400 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 3]
def baseStart_380400 : Nat := 118140960795 + 380400 * 2 ^ 59
def prefixEnd_380400 : Nat := 4983230072969 + 3 ^ 40 * 380400 * 2
def baseEnd_380400 : Nat := 173624925307037259511625

theorem tailTrace_380400 : CollatzResearch.WordTrace tailWord_380400 prefixEnd_380400 173624925307037259511625 := by
  unfold tailWord_380400
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937163910941620996405327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9249551881255494661873769 6937163910941620996405327)
  ·
    refine ⟨10405745866412431494607991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6937163910941620996405327 10405745866412431494607991)
    ·
      refine ⟨15608618799618647241911987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10405745866412431494607991 15608618799618647241911987)
      ·
        refine ⟨23412928199427970862867981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15608618799618647241911987 23412928199427970862867981)
        ·
          refine ⟨8779848074785489073575493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23412928199427970862867981 8779848074785489073575493)
          ·
            refine ⟨1646221514022279201295405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8779848074785489073575493 1646221514022279201295405)
            ·
              refine ⟨617333067758354700485777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1646221514022279201295405 617333067758354700485777)
              ·
                refine ⟨462999800818766025364333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617333067758354700485777 462999800818766025364333)
                ·
                  refine ⟨173624925307037259511625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462999800818766025364333 173624925307037259511625)
                  ·
                    rfl

theorem cell20_380400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_380400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380400 prefixEnd_380400 := by exact prefixLift 380400
  have htrace : WordTrace (prefixWord ++ tailWord_380400) baseStart_380400 baseEnd_380400 := by
    simpa [prefixWord, tailWord_380400, baseEnd_380400] using wordTrace_append hprefix tailTrace_380400
  have hstable : (prefixWord ++ tailWord_380400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380400).length < 2 ^ (prefixWord ++ tailWord_380400).sum := by decide
  have hdescent : baseEnd_380400 < baseStart_380400 := by decide
  rcases family_descends (prefixWord ++ tailWord_380400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380462 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_380462 : Nat := 118140960795 + 380462 * 2 ^ 59
def prefixEnd_380462 : Nat := 4983230072969 + 3 ^ 40 * 380462 * 2
def baseEnd_380462 : Nat := 173653223796440599444705

theorem tailTrace_380462 : CollatzResearch.WordTrace tailWord_380462 prefixEnd_380462 173653223796440599444705 := by
  unfold tailWord_380462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734573643457328322695955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9251059431772417721045093 1734573643457328322695955)
  ·
    refine ⟨2601860465185992484043933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1734573643457328322695955 2601860465185992484043933)
    ·
      refine ⟨975697674444747181516475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2601860465185992484043933 975697674444747181516475)
      ·
        refine ⟨1463546511667120772274713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 975697674444747181516475 1463546511667120772274713)
        ·
          refine ⟨1097659883750340579206035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1463546511667120772274713 1097659883750340579206035)
          ·
            refine ⟨1646489825625510868809053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097659883750340579206035 1646489825625510868809053)
            ·
              refine ⟨617433684609566575803395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1646489825625510868809053 617433684609566575803395)
              ·
                refine ⟨926150526914349863705093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617433684609566575803395 926150526914349863705093)
                ·
                  refine ⟨173653223796440599444705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 926150526914349863705093 173653223796440599444705)
                  ·
                    rfl

theorem cell20_380462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_380462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380462 prefixEnd_380462 := by exact prefixLift 380462
  have htrace : WordTrace (prefixWord ++ tailWord_380462) baseStart_380462 baseEnd_380462 := by
    simpa [prefixWord, tailWord_380462, baseEnd_380462] using wordTrace_append hprefix tailTrace_380462
  have hstable : (prefixWord ++ tailWord_380462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380462).length < 2 ^ (prefixWord ++ tailWord_380462).sum := by decide
  have hdescent : baseEnd_380462 < baseStart_380462 := by decide
  rcases family_descends (prefixWord ++ tailWord_380462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380500 : List Nat := [2, 4, 1, 1, 1, 2, 2, 5, 2]
def baseStart_380500 : Nat := 118140960795 + 380500 * 2 ^ 59
def prefixEnd_380500 : Nat := 4983230072969 + 3 ^ 40 * 380500 * 2
def baseEnd_380500 : Nat := 173670568031881356177883

theorem tailTrace_380500 : CollatzResearch.WordTrace tailWord_380500 prefixEnd_380500 173670568031881356177883 := by
  unfold tailWord_380500
  simp only [CollatzResearch.WordTrace]
  refine ⟨6938987560760479535725477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9251983414347306047633969 6938987560760479535725477)
  ·
    refine ⟨1301060167642589912948527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6938987560760479535725477 1301060167642589912948527)
    ·
      refine ⟨1951590251463884869422791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301060167642589912948527 1951590251463884869422791)
      ·
        refine ⟨2927385377195827304134187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951590251463884869422791 2927385377195827304134187)
        ·
          refine ⟨4391078065793740956201281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2927385377195827304134187 4391078065793740956201281)
          ·
            refine ⟨3293308549345305717150961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4391078065793740956201281 3293308549345305717150961)
            ·
              refine ⟨2469981412008979287863221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3293308549345305717150961 2469981412008979287863221)
              ·
                refine ⟨231560757375841808237177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2469981412008979287863221 231560757375841808237177)
                ·
                  refine ⟨173670568031881356177883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231560757375841808237177 173670568031881356177883)
                  ·
                    rfl

theorem cell20_380500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_380500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380500 prefixEnd_380500 := by exact prefixLift 380500
  have htrace : WordTrace (prefixWord ++ tailWord_380500) baseStart_380500 baseEnd_380500 := by
    simpa [prefixWord, tailWord_380500, baseEnd_380500] using wordTrace_append hprefix tailTrace_380500
  have hstable : (prefixWord ++ tailWord_380500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380500).length < 2 ^ (prefixWord ++ tailWord_380500).sum := by decide
  have hdescent : baseEnd_380500 < baseStart_380500 := by decide
  rcases family_descends (prefixWord ++ tailWord_380500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380517 : List Nat := [1, 3, 1, 3, 3, 1, 4, 2, 2]
def baseStart_380517 : Nat := 118140960795 + 380517 * 2 ^ 59
def prefixEnd_380517 : Nat := 4983230072969 + 3 ^ 40 * 380517 * 2
def baseEnd_380517 : Nat := 173678327295104852611147

theorem tailTrace_380517 : CollatzResearch.WordTrace tailWord_380517 prefixEnd_380517 173678327295104852611147 := by
  unfold tailWord_380517
  simp only [CollatzResearch.WordTrace]
  refine ⟨13878595162459370974819805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9252396774972913983213203 13878595162459370974819805)
  ·
    refine ⟨5204473185922264115557427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13878595162459370974819805 5204473185922264115557427)
    ·
      refine ⟨7806709778883396173336141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5204473185922264115557427 7806709778883396173336141)
      ·
        refine ⟨2927516167081273565001053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7806709778883396173336141 2927516167081273565001053)
        ·
          refine ⟨1097818562655477586875395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2927516167081273565001053 1097818562655477586875395)
          ·
            refine ⟨1646727843983216380313093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097818562655477586875395 1646727843983216380313093)
            ·
              refine ⟨308761470746853071308705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1646727843983216380313093 308761470746853071308705)
              ·
                refine ⟨231571103060139803481529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308761470746853071308705 231571103060139803481529)
                ·
                  refine ⟨173678327295104852611147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231571103060139803481529 173678327295104852611147)
                  ·
                    rfl

theorem cell20_380517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_380517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380517 prefixEnd_380517 := by exact prefixLift 380517
  have htrace : WordTrace (prefixWord ++ tailWord_380517) baseStart_380517 baseEnd_380517 := by
    simpa [prefixWord, tailWord_380517, baseEnd_380517] using wordTrace_append hprefix tailTrace_380517
  have hstable : (prefixWord ++ tailWord_380517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380517).length < 2 ^ (prefixWord ++ tailWord_380517).sum := by decide
  have hdescent : baseEnd_380517 < baseStart_380517 := by decide
  rcases family_descends (prefixWord ++ tailWord_380517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380528 : List Nat := [2, 1, 1, 1, 6, 1, 3, 5]
def baseStart_380528 : Nat := 118140960795 + 380528 * 2 ^ 59
def prefixEnd_380528 : Nat := 4983230072969 + 3 ^ 40 * 380528 * 2
def baseEnd_380528 : Nat := 57894449331612567748145

theorem tailTrace_380528 : CollatzResearch.WordTrace tailWord_380528 prefixEnd_380528 57894449331612567748145 := by
  unfold tailWord_380528
  simp only [CollatzResearch.WordTrace]
  refine ⟨6939498182709759926735119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9252664243613013235646825 6939498182709759926735119)
  ·
    refine ⟨10409247274064639890102679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6939498182709759926735119 10409247274064639890102679)
    ·
      refine ⟨15613870911096959835154019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10409247274064639890102679 15613870911096959835154019)
      ·
        refine ⟨23420806366645439752731029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15613870911096959835154019 23420806366645439752731029)
        ·
          refine ⟨1097850298436504988409267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23420806366645439752731029 1097850298436504988409267)
          ·
            refine ⟨1646775447654757482613901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097850298436504988409267 1646775447654757482613901)
            ·
              refine ⟨617540792870534055980213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1646775447654757482613901 617540792870534055980213)
              ·
                refine ⟨57894449331612567748145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 617540792870534055980213 57894449331612567748145)
                ·
                  rfl

theorem cell20_380528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_380528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380528 prefixEnd_380528 := by exact prefixLift 380528
  have htrace : WordTrace (prefixWord ++ tailWord_380528) baseStart_380528 baseEnd_380528 := by
    simpa [prefixWord, tailWord_380528, baseEnd_380528] using wordTrace_append hprefix tailTrace_380528
  have hstable : (prefixWord ++ tailWord_380528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380528).length < 2 ^ (prefixWord ++ tailWord_380528).sum := by decide
  have hdescent : baseEnd_380528 < baseStart_380528 := by decide
  rcases family_descends (prefixWord ++ tailWord_380528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380545 : List Nat := [1, 2, 4, 2, 1, 3, 3, 4]
def baseStart_380545 : Nat := 118140960795 + 380545 * 2 ^ 59
def prefixEnd_380545 : Nat := 4983230072969 + 3 ^ 40 * 380545 * 2
def baseEnd_380545 : Nat := 57897035752687066559233

theorem tailTrace_380545 : CollatzResearch.WordTrace tailWord_380545 prefixEnd_380545 57897035752687066559233 := by
  unfold tailWord_380545
  simp only [CollatzResearch.WordTrace]
  refine ⟨13879616406357931756839089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9253077604238621171226059 13879616406357931756839089)
  ·
    refine ⟨10409712304768448817629317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13879616406357931756839089 10409712304768448817629317)
    ·
      refine ⟨1951821057144084153305497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10409712304768448817629317 1951821057144084153305497)
      ·
        refine ⟨1463865792858063114979123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1951821057144084153305497 1463865792858063114979123)
        ·
          refine ⟨2195798689287094672468685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463865792858063114979123 2195798689287094672468685)
          ·
            refine ⟨823424508482660502175757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2195798689287094672468685 823424508482660502175757)
            ·
              refine ⟨308784190680997688315909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 823424508482660502175757 308784190680997688315909)
              ·
                refine ⟨57897035752687066559233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308784190680997688315909 57897035752687066559233)
                ·
                  rfl

theorem cell20_380545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 4].length) (baseStart_380545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380545 prefixEnd_380545 := by exact prefixLift 380545
  have htrace : WordTrace (prefixWord ++ tailWord_380545) baseStart_380545 baseEnd_380545 := by
    simpa [prefixWord, tailWord_380545, baseEnd_380545] using wordTrace_append hprefix tailTrace_380545
  have hstable : (prefixWord ++ tailWord_380545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380545).length < 2 ^ (prefixWord ++ tailWord_380545).sum := by decide
  have hdescent : baseEnd_380545 < baseStart_380545 := by decide
  rcases family_descends (prefixWord ++ tailWord_380545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380576 : List Nat := [2, 1, 1, 4, 3, 1, 2, 4, 2]
def baseStart_380576 : Nat := 118140960795 + 380576 * 2 ^ 59
def prefixEnd_380576 : Nat := 4983230072969 + 3 ^ 40 * 380576 * 2
def baseEnd_380576 : Nat := 173705256502762869644239

theorem tailTrace_380576 : CollatzResearch.WordTrace tailWord_380576 prefixEnd_380576 173705256502762869644239 := by
  unfold tailWord_380576
  simp only [CollatzResearch.WordTrace]
  refine ⟨6940373534622812025608791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9253831379497082700811721 6940373534622812025608791)
  ·
    refine ⟨10410560301934218038413187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6940373534622812025608791 10410560301934218038413187)
    ·
      refine ⟨15615840452901327057619781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10410560301934218038413187 15615840452901327057619781)
      ·
        refine ⟨2927970084918998823303709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15615840452901327057619781 2927970084918998823303709)
        ·
          refine ⟨1097988781844624558738891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2927970084918998823303709 1097988781844624558738891)
          ·
            refine ⟨1646983172766936838108337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097988781844624558738891 1646983172766936838108337)
            ·
              refine ⟨1235237379575202628581253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646983172766936838108337 1235237379575202628581253)
              ·
                refine ⟨231607008670350492858985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1235237379575202628581253 231607008670350492858985)
                ·
                  refine ⟨173705256502762869644239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231607008670350492858985 173705256502762869644239)
                  ·
                    rfl

theorem cell20_380576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_380576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380576 prefixEnd_380576 := by exact prefixLift 380576
  have htrace : WordTrace (prefixWord ++ tailWord_380576) baseStart_380576 baseEnd_380576 := by
    simpa [prefixWord, tailWord_380576, baseEnd_380576] using wordTrace_append hprefix tailTrace_380576
  have hstable : (prefixWord ++ tailWord_380576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380576).length < 2 ^ (prefixWord ++ tailWord_380576).sum := by decide
  have hdescent : baseEnd_380576 < baseStart_380576 := by decide
  rcases family_descends (prefixWord ++ tailWord_380576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380604 : List Nat := [2, 2, 2, 3, 1, 3, 1, 6]
def baseStart_380604 : Nat := 118140960795 + 380604 * 2 ^ 59
def prefixEnd_380604 : Nat := 4983230072969 + 3 ^ 40 * 380604 * 2
def baseEnd_380604 : Nat := 57906012155239738903597

theorem tailTrace_380604 : CollatzResearch.WordTrace tailWord_380604 prefixEnd_380604 57906012155239738903597 := by
  unfold tailWord_380604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6940884156572092416618433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9254512208762789888824577 6940884156572092416618433)
  ·
    refine ⟨5205663117429069312463825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6940884156572092416618433 5205663117429069312463825)
    ·
      refine ⟨3904247338071801984347869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5205663117429069312463825 3904247338071801984347869)
      ·
        refine ⟨1464092751776925744130451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3904247338071801984347869 1464092751776925744130451)
        ·
          refine ⟨2196139127665388616195677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464092751776925744130451 2196139127665388616195677)
          ·
            refine ⟨823552172874520731073379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2196139127665388616195677 823552172874520731073379)
            ·
              refine ⟨1235328259311781096610069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823552172874520731073379 1235328259311781096610069)
              ·
                refine ⟨57906012155239738903597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1235328259311781096610069 57906012155239738903597)
                ·
                  rfl

theorem cell20_380604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_380604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380604 prefixEnd_380604 := by exact prefixLift 380604
  have htrace : WordTrace (prefixWord ++ tailWord_380604) baseStart_380604 baseEnd_380604 := by
    simpa [prefixWord, tailWord_380604, baseEnd_380604] using wordTrace_append hprefix tailTrace_380604
  have hstable : (prefixWord ++ tailWord_380604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380604).length < 2 ^ (prefixWord ++ tailWord_380604).sum := by decide
  have hdescent : baseEnd_380604 < baseStart_380604 := by decide
  rcases family_descends (prefixWord ++ tailWord_380604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380621 : List Nat := [1, 6, 2, 1, 1, 1, 8]
def baseStart_380621 : Nat := 118140960795 + 380621 * 2 ^ 59
def prefixEnd_380621 : Nat := 4983230072969 + 3 ^ 40 * 380621 * 2
def baseEnd_380621 : Nat := 19302866192104745904895

theorem tailTrace_380621 : CollatzResearch.WordTrace tailWord_380621 prefixEnd_380621 19302866192104745904895 := by
  unfold tailWord_380621
  simp only [CollatzResearch.WordTrace]
  refine ⟨13882388354082596736605717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9254925569388397824403811 13882388354082596736605717)
  ·
    refine ⟨650736954097621722028393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13882388354082596736605717 650736954097621722028393)
    ·
      refine ⟨488052715573216291521295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 650736954097621722028393 488052715573216291521295)
      ·
        refine ⟨732079073359824437281943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488052715573216291521295 732079073359824437281943)
        ·
          refine ⟨1098118610039736655922915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732079073359824437281943 1098118610039736655922915)
          ·
            refine ⟨1647177915059604983884373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098118610039736655922915 1647177915059604983884373)
            ·
              refine ⟨19302866192104745904895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1647177915059604983884373 19302866192104745904895)
              ·
                rfl

theorem cell20_380621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 8].length) (baseStart_380621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380621 prefixEnd_380621 := by exact prefixLift 380621
  have htrace : WordTrace (prefixWord ++ tailWord_380621) baseStart_380621 baseEnd_380621 := by
    simpa [prefixWord, tailWord_380621, baseEnd_380621] using wordTrace_append hprefix tailTrace_380621
  have hstable : (prefixWord ++ tailWord_380621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380621).length < 2 ^ (prefixWord ++ tailWord_380621).sum := by decide
  have hdescent : baseEnd_380621 < baseStart_380621 := by decide
  rcases family_descends (prefixWord ++ tailWord_380621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380625 : List Nat := [1, 2, 2, 1, 2, 4, 8]
def baseStart_380625 : Nat := 118140960795 + 380625 * 2 ^ 59
def prefixEnd_380625 : Nat := 4983230072969 + 3 ^ 40 * 380625 * 2
def baseEnd_380625 : Nat := 19303069048659608556745

theorem tailTrace_380625 : CollatzResearch.WordTrace tailWord_380625 prefixEnd_380625 19303069048659608556745 := by
  unfold tailWord_380625
  simp only [CollatzResearch.WordTrace]
  refine ⟨13882534246068105419751329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9255022830712070279834219 13882534246068105419751329)
  ·
    refine ⟨10411900684551079064813497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13882534246068105419751329 10411900684551079064813497)
    ·
      refine ⟨7808925513413309298610123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10411900684551079064813497 7808925513413309298610123)
      ·
        refine ⟨11713388270119963947915185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7808925513413309298610123 11713388270119963947915185)
        ·
          refine ⟨8785041202589972960936389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11713388270119963947915185 8785041202589972960936389)
          ·
            refine ⟨1647195225485619930175573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8785041202589972960936389 1647195225485619930175573)
            ·
              refine ⟨19303069048659608556745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1647195225485619930175573 19303069048659608556745)
              ·
                rfl

theorem cell20_380625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 8].length) (baseStart_380625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380625 prefixEnd_380625 := by exact prefixLift 380625
  have htrace : WordTrace (prefixWord ++ tailWord_380625) baseStart_380625 baseEnd_380625 := by
    simpa [prefixWord, tailWord_380625, baseEnd_380625] using wordTrace_append hprefix tailTrace_380625
  have hstable : (prefixWord ++ tailWord_380625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380625).length < 2 ^ (prefixWord ++ tailWord_380625).sum := by decide
  have hdescent : baseEnd_380625 < baseStart_380625 := by decide
  rcases family_descends (prefixWord ++ tailWord_380625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380628 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_380628 : Nat := 118140960795 + 380628 * 2 ^ 59
def prefixEnd_380628 : Nat := 4983230072969 + 3 ^ 40 * 380628 * 2
def baseEnd_380628 : Nat := 173728990719681799910693

theorem tailTrace_380628 : CollatzResearch.WordTrace tailWord_380628 prefixEnd_380628 173728990719681799910693 := by
  unfold tailWord_380628
  simp only [CollatzResearch.WordTrace]
  refine ⟨6941321832528618466055269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9255095776704824621407025 6941321832528618466055269)
  ·
    refine ⟨1301497843599115962385363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6941321832528618466055269 1301497843599115962385363)
    ·
      refine ⟨1952246765398673943578045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301497843599115962385363 1952246765398673943578045)
      ·
        refine ⟨732092537024502728841767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1952246765398673943578045 732092537024502728841767)
        ·
          refine ⟨1098138805536754093262651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732092537024502728841767 1098138805536754093262651)
          ·
            refine ⟨1647208208305131139893977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098138805536754093262651 1647208208305131139893977)
            ·
              refine ⟨1235406156228848354920483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1647208208305131139893977 1235406156228848354920483)
              ·
                refine ⟨1853109234343272532380725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235406156228848354920483 1853109234343272532380725)
                ·
                  refine ⟨173728990719681799910693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1853109234343272532380725 173728990719681799910693)
                  ·
                    rfl

theorem cell20_380628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_380628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380628 prefixEnd_380628 := by exact prefixLift 380628
  have htrace : WordTrace (prefixWord ++ tailWord_380628) baseStart_380628 baseEnd_380628 := by
    simpa [prefixWord, tailWord_380628, baseEnd_380628] using wordTrace_append hprefix tailTrace_380628
  have hstable : (prefixWord ++ tailWord_380628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380628).length < 2 ^ (prefixWord ++ tailWord_380628).sum := by decide
  have hdescent : baseEnd_380628 < baseStart_380628 := by decide
  rcases family_descends (prefixWord ++ tailWord_380628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380663 : List Nat := [1, 1, 3, 1, 1, 1, 6, 6]
def baseStart_380663 : Nat := 118140960795 + 380663 * 2 ^ 59
def prefixEnd_380663 : Nat := 4983230072969 + 3 ^ 40 * 380663 * 2
def baseEnd_380663 : Nat := 57914988557792411247961

theorem tailTrace_380663 : CollatzResearch.WordTrace tailWord_380663 prefixEnd_380663 57914988557792411247961 := by
  unfold tailWord_380663
  simp only [CollatzResearch.WordTrace]
  refine ⟨13883920219930437909634643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9255946813286958606423095 13883920219930437909634643)
  ·
    refine ⟨20825880329895656864451965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13883920219930437909634643 20825880329895656864451965)
    ·
      refine ⟨7809705123710871324169487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20825880329895656864451965 7809705123710871324169487)
      ·
        refine ⟨11714557685566306986254231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7809705123710871324169487 11714557685566306986254231)
        ·
          refine ⟨17571836528349460479381347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11714557685566306986254231 17571836528349460479381347)
          ·
            refine ⟨26357754792524190719072021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17571836528349460479381347 26357754792524190719072021)
            ·
              refine ⟨1235519755899571439956501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26357754792524190719072021 1235519755899571439956501)
              ·
                refine ⟨57914988557792411247961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1235519755899571439956501 57914988557792411247961)
                ·
                  rfl

theorem cell20_380663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_380663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380663 prefixEnd_380663 := by exact prefixLift 380663
  have htrace : WordTrace (prefixWord ++ tailWord_380663) baseStart_380663 baseEnd_380663 := by
    simpa [prefixWord, tailWord_380663, baseEnd_380663] using wordTrace_append hprefix tailTrace_380663
  have hstable : (prefixWord ++ tailWord_380663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380663).length < 2 ^ (prefixWord ++ tailWord_380663).sum := by decide
  have hdescent : baseEnd_380663 < baseStart_380663 := by decide
  rcases family_descends (prefixWord ++ tailWord_380663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380678 : List Nat := [6, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_380678 : Nat := 118140960795 + 380678 * 2 ^ 59
def prefixEnd_380678 : Nat := 4983230072969 + 3 ^ 40 * 380678 * 2
def baseEnd_380678 : Nat := 173751812082103848243823

theorem tailTrace_380678 : CollatzResearch.WordTrace tailWord_380678 prefixEnd_380678 173751812082103848243823 := by
  unfold tailWord_380678
  simp only [CollatzResearch.WordTrace]
  refine ⟨433889603589877983482209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9256311543250730314287125 433889603589877983482209)
  ·
    refine ⟨325417202692408487611657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 433889603589877983482209 325417202692408487611657)
    ·
      refine ⟨244062902019306365708743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325417202692408487611657 244062902019306365708743)
      ·
        refine ⟨366094353028959548563115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244062902019306365708743 366094353028959548563115)
        ·
          refine ⟨549141529543439322844673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366094353028959548563115 549141529543439322844673)
          ·
            refine ⟨411856147157579492133505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549141529543439322844673 411856147157579492133505)
            ·
              refine ⟨308892110368184619100129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411856147157579492133505 308892110368184619100129)
              ·
                refine ⟨231669082776138464325097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308892110368184619100129 231669082776138464325097)
                ·
                  refine ⟨173751812082103848243823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231669082776138464325097 173751812082103848243823)
                  ·
                    rfl

theorem cell20_380678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_380678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380678 prefixEnd_380678 := by exact prefixLift 380678
  have htrace : WordTrace (prefixWord ++ tailWord_380678) baseStart_380678 baseEnd_380678 := by
    simpa [prefixWord, tailWord_380678, baseEnd_380678] using wordTrace_append hprefix tailTrace_380678
  have hstable : (prefixWord ++ tailWord_380678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380678).length < 2 ^ (prefixWord ++ tailWord_380678).sum := by decide
  have hdescent : baseEnd_380678 < baseStart_380678 := by decide
  rcases family_descends (prefixWord ++ tailWord_380678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380728 : List Nat := [2, 1, 2, 1, 3, 4, 2, 3, 2]
def baseStart_380728 : Nat := 118140960795 + 380728 * 2 ^ 59
def prefixEnd_380728 : Nat := 4983230072969 + 3 ^ 40 * 380728 * 2
def baseEnd_380728 : Nat := 173774633444525896576951

theorem tailTrace_380728 : CollatzResearch.WordTrace tailWord_380728 prefixEnd_380728 173774633444525896576951 := by
  unfold tailWord_380728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6943145482347477005375419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9257527309796636007167225 6943145482347477005375419)
  ·
    refine ⟨10414718223521215508063129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6943145482347477005375419 10414718223521215508063129)
    ·
      refine ⟨7811038667640911631047347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10414718223521215508063129 7811038667640911631047347)
      ·
        refine ⟨11716558001461367446571021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7811038667640911631047347 11716558001461367446571021)
        ·
          refine ⟨4393709250548012792464133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11716558001461367446571021 4393709250548012792464133)
          ·
            refine ⟨823820484477752398587025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4393709250548012792464133 823820484477752398587025)
            ·
              refine ⟨617865363358314298940269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823820484477752398587025 617865363358314298940269)
              ·
                refine ⟨231699511259367862102601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617865363358314298940269 231699511259367862102601)
                ·
                  refine ⟨173774633444525896576951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231699511259367862102601 173774633444525896576951)
                  ·
                    rfl

theorem cell20_380728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_380728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380728 prefixEnd_380728 := by exact prefixLift 380728
  have htrace : WordTrace (prefixWord ++ tailWord_380728) baseStart_380728 baseEnd_380728 := by
    simpa [prefixWord, tailWord_380728, baseEnd_380728] using wordTrace_append hprefix tailTrace_380728
  have hstable : (prefixWord ++ tailWord_380728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380728).length < 2 ^ (prefixWord ++ tailWord_380728).sum := by decide
  have hdescent : baseEnd_380728 < baseStart_380728 := by decide
  rcases family_descends (prefixWord ++ tailWord_380728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380739 : List Nat := [1, 1, 1, 3, 1, 6, 7]
def baseStart_380739 : Nat := 118140960795 + 380739 * 2 ^ 59
def prefixEnd_380739 : Nat := 4983230072969 + 3 ^ 40 * 380739 * 2
def baseEnd_380739 : Nat := 19308850460473194134471

theorem tailTrace_380739 : CollatzResearch.WordTrace tailWord_380739 prefixEnd_380739 19308850460473194134471 := by
  unfold tailWord_380739
  simp only [CollatzResearch.WordTrace]
  refine ⟨13886692167655102889401271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9257794778436735259600847 13886692167655102889401271)
  ·
    refine ⟨20830038251482654334101907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13886692167655102889401271 20830038251482654334101907)
    ·
      refine ⟨31245057377223981501152861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20830038251482654334101907 31245057377223981501152861)
      ·
        refine ⟨11716896516458993062932323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31245057377223981501152861 11716896516458993062932323)
        ·
          refine ⟨17575344774688489594398485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11716896516458993062932323 17575344774688489594398485)
          ·
            refine ⟨823844286313522949737429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17575344774688489594398485 823844286313522949737429)
            ·
              refine ⟨19308850460473194134471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 823844286313522949737429 19308850460473194134471)
              ·
                rfl

theorem cell20_380739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 7].length) (baseStart_380739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380739 prefixEnd_380739 := by exact prefixLift 380739
  have htrace : WordTrace (prefixWord ++ tailWord_380739) baseStart_380739 baseEnd_380739 := by
    simpa [prefixWord, tailWord_380739, baseEnd_380739] using wordTrace_append hprefix tailTrace_380739
  have hstable : (prefixWord ++ tailWord_380739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380739).length < 2 ^ (prefixWord ++ tailWord_380739).sum := by decide
  have hdescent : baseEnd_380739 < baseStart_380739 := by decide
  rcases family_descends (prefixWord ++ tailWord_380739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380759 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 3]
def baseStart_380759 : Nat := 118140960795 + 380759 * 2 ^ 59
def prefixEnd_380759 : Nat := 4983230072969 + 3 ^ 40 * 380759 * 2
def baseEnd_380759 : Nat := 173788782689227566543491

theorem tailTrace_380759 : CollatzResearch.WordTrace tailWord_380759 prefixEnd_380759 173788782689227566543491 := by
  unfold tailWord_380759
  simp only [CollatzResearch.WordTrace]
  refine ⟨13887421627582646305129331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9258281085055097536752887 13887421627582646305129331)
  ·
    refine ⟨20831132441373969457693997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13887421627582646305129331 20831132441373969457693997)
    ·
      refine ⟨7811674665515238546635249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20831132441373969457693997 7811674665515238546635249)
      ·
        refine ⟨5858755999136428909976437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7811674665515238546635249 5858755999136428909976437)
        ·
          refine ⟨549258374919040210310291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5858755999136428909976437 549258374919040210310291)
          ·
            refine ⟨823887562378560315465437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549258374919040210310291 823887562378560315465437)
            ·
              refine ⟨308957835891960118299539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 823887562378560315465437 308957835891960118299539)
              ·
                refine ⟨463436753837940177449309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308957835891960118299539 463436753837940177449309)
                ·
                  refine ⟨173788782689227566543491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463436753837940177449309 173788782689227566543491)
                  ·
                    rfl

theorem cell20_380759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 3].length) (baseStart_380759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380759 prefixEnd_380759 := by exact prefixLift 380759
  have htrace : WordTrace (prefixWord ++ tailWord_380759) baseStart_380759 baseEnd_380759 := by
    simpa [prefixWord, tailWord_380759, baseEnd_380759] using wordTrace_append hprefix tailTrace_380759
  have hstable : (prefixWord ++ tailWord_380759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380759).length < 2 ^ (prefixWord ++ tailWord_380759).sum := by decide
  have hdescent : baseEnd_380759 < baseStart_380759 := by decide
  rcases family_descends (prefixWord ++ tailWord_380759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380790 : List Nat := [5, 1, 1, 3, 3, 1, 6]
def baseStart_380790 : Nat := 118140960795 + 380790 * 2 ^ 59
def prefixEnd_380790 : Nat := 4983230072969 + 3 ^ 40 * 380790 * 2
def baseEnd_380790 : Nat := 19311436881547692945559

theorem tailTrace_380790 : CollatzResearch.WordTrace tailWord_380790 prefixEnd_380790 19311436881547692945559 := by
  unfold tailWord_380790
  simp only [CollatzResearch.WordTrace]
  refine ⟨868034518154396162469239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9259034860313559066338549 868034518154396162469239)
  ·
    refine ⟨1302051777231594243703859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 868034518154396162469239 1302051777231594243703859)
    ·
      refine ⟨1953077665847391365555789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302051777231594243703859 1953077665847391365555789)
      ·
        refine ⟨732404124692771762083421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1953077665847391365555789 732404124692771762083421)
        ·
          refine ⟨274651546759789410781283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 732404124692771762083421 274651546759789410781283)
          ·
            refine ⟨411977320139684116171925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274651546759789410781283 411977320139684116171925)
            ·
              refine ⟨19311436881547692945559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 411977320139684116171925 19311436881547692945559)
              ·
                rfl

theorem cell20_380790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 6].length) (baseStart_380790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380790 prefixEnd_380790 := by exact prefixLift 380790
  have htrace : WordTrace (prefixWord ++ tailWord_380790) baseStart_380790 baseEnd_380790 := by
    simpa [prefixWord, tailWord_380790, baseEnd_380790] using wordTrace_append hprefix tailTrace_380790
  have hstable : (prefixWord ++ tailWord_380790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380790).length < 2 ^ (prefixWord ++ tailWord_380790).sum := by decide
  have hdescent : baseEnd_380790 < baseStart_380790 := by decide
  rcases family_descends (prefixWord ++ tailWord_380790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380852 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 3]
def baseStart_380852 : Nat := 118140960795 + 380852 * 2 ^ 59
def prefixEnd_380852 : Nat := 4983230072969 + 3 ^ 40 * 380852 * 2
def baseEnd_380852 : Nat := 173831230423332576443111

theorem tailTrace_380852 : CollatzResearch.WordTrace tailWord_380852 prefixEnd_380852 173831230423332576443111 := by
  unfold tailWord_380852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945406808122861594132405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9260542410830482125509873 6945406808122861594132405)
  ·
    refine ⟨651131888261518274449913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6945406808122861594132405 651131888261518274449913)
    ·
      refine ⟨488348916196138705837435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 651131888261518274449913 488348916196138705837435)
      ·
        refine ⟨732523374294208058756153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488348916196138705837435 732523374294208058756153)
        ·
          refine ⟨549392530720656044067115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732523374294208058756153 549392530720656044067115)
          ·
            refine ⟨824088796080984066100673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549392530720656044067115 824088796080984066100673)
            ·
              refine ⟨618066597060738049575505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824088796080984066100673 618066597060738049575505)
              ·
                refine ⟨463549947795553537181629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 618066597060738049575505 463549947795553537181629)
                ·
                  refine ⟨173831230423332576443111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463549947795553537181629 173831230423332576443111)
                  ·
                    rfl

theorem cell20_380852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_380852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380852 prefixEnd_380852 := by exact prefixLift 380852
  have htrace : WordTrace (prefixWord ++ tailWord_380852) baseStart_380852 baseEnd_380852 := by
    simpa [prefixWord, tailWord_380852, baseEnd_380852] using wordTrace_append hprefix tailTrace_380852
  have hstable : (prefixWord ++ tailWord_380852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380852).length < 2 ^ (prefixWord ++ tailWord_380852).sum := by decide
  have hdescent : baseEnd_380852 < baseStart_380852 := by decide
  rcases family_descends (prefixWord ++ tailWord_380852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380853 : List Nat := [1, 3, 3, 2, 1, 10]
def baseStart_380853 : Nat := 118140960795 + 380853 * 2 ^ 59
def prefixEnd_380853 : Nat := 4983230072969 + 3 ^ 40 * 380853 * 2
def baseEnd_380853 : Nat := 6438210624095593237399

theorem tailTrace_380853 : CollatzResearch.WordTrace tailWord_380853 prefixEnd_380853 6438210624095593237399 := by
  unfold tailWord_380853
  simp only [CollatzResearch.WordTrace]
  refine ⟨13890850089242100359051213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9260566726161400239367475 13890850089242100359051213)
  ·
    refine ⟨5209068783465787634644205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13890850089242100359051213 5209068783465787634644205)
    ·
      refine ⟨1953400793799670362991577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5209068783465787634644205 1953400793799670362991577)
      ·
        refine ⟨1465050595349752772243683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1953400793799670362991577 1465050595349752772243683)
        ·
          refine ⟨2197575893024629158365525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465050595349752772243683 2197575893024629158365525)
          ·
            refine ⟨6438210624095593237399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2197575893024629158365525 6438210624095593237399)
            ·
              rfl

theorem cell20_380853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 10].length) (baseStart_380853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380853 prefixEnd_380853 := by exact prefixLift 380853
  have htrace : WordTrace (prefixWord ++ tailWord_380853) baseStart_380853 baseEnd_380853 := by
    simpa [prefixWord, tailWord_380853, baseEnd_380853] using wordTrace_append hprefix tailTrace_380853
  have hstable : (prefixWord ++ tailWord_380853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380853).length < 2 ^ (prefixWord ++ tailWord_380853).sum := by decide
  have hdescent : baseEnd_380853 < baseStart_380853 := by decide
  rcases family_descends (prefixWord ++ tailWord_380853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380863 : List Nat := [1, 1, 2, 2, 2, 1, 5, 4, 2]
def baseStart_380863 : Nat := 118140960795 + 380863 * 2 ^ 59
def prefixEnd_380863 : Nat := 4983230072969 + 3 ^ 40 * 380863 * 2
def baseEnd_380863 : Nat := 173836251123065427076399

theorem tailTrace_380863 : CollatzResearch.WordTrace tailWord_380863 prefixEnd_380863 173836251123065427076399 := by
  unfold tailWord_380863
  simp only [CollatzResearch.WordTrace]
  refine ⟨13891214819205872066915243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9260809879470581377943495 13891214819205872066915243)
  ·
    refine ⟨20836822228808808100372865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13891214819205872066915243 20836822228808808100372865)
    ·
      refine ⟨15627616671606606075279649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20836822228808808100372865 15627616671606606075279649)
      ·
        refine ⟨11720712503704954556459737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15627616671606606075279649 11720712503704954556459737)
        ·
          refine ⟨8790534377778715917344803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11720712503704954556459737 8790534377778715917344803)
          ·
            refine ⟨13185801566668073876017205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8790534377778715917344803 13185801566668073876017205)
            ·
              refine ⟨1236168896875131925876613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13185801566668073876017205 1236168896875131925876613)
              ·
                refine ⟨231781668164087236101865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1236168896875131925876613 231781668164087236101865)
                ·
                  refine ⟨173836251123065427076399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231781668164087236101865 173836251123065427076399)
                  ·
                    rfl

theorem cell20_380863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 2].length) (baseStart_380863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380863 prefixEnd_380863 := by exact prefixLift 380863
  have htrace : WordTrace (prefixWord ++ tailWord_380863) baseStart_380863 baseEnd_380863 := by
    simpa [prefixWord, tailWord_380863, baseEnd_380863] using wordTrace_append hprefix tailTrace_380863
  have hstable : (prefixWord ++ tailWord_380863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380863).length < 2 ^ (prefixWord ++ tailWord_380863).sum := by decide
  have hdescent : baseEnd_380863 < baseStart_380863 := by decide
  rcases family_descends (prefixWord ++ tailWord_380863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380918 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_380918 : Nat := 118140960795 + 380918 * 2 ^ 59
def prefixEnd_380918 : Nat := 4983230072969 + 3 ^ 40 * 380918 * 2
def baseEnd_380918 : Nat := 173861354621729680242841

theorem tailTrace_380918 : CollatzResearch.WordTrace tailWord_380918 prefixEnd_380918 173861354621729680242841 := by
  unfold tailWord_380918
  simp only [CollatzResearch.WordTrace]
  refine ⟨868326302125413528760463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9262147222671077640111605 868326302125413528760463)
  ·
    refine ⟨1302489453188120293140695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 868326302125413528760463 1302489453188120293140695)
    ·
      refine ⟨1953734179782180439711043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302489453188120293140695 1953734179782180439711043)
      ·
        refine ⟨2930601269673270659566565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953734179782180439711043 2930601269673270659566565)
        ·
          refine ⟨549487738063738248668731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2930601269673270659566565 549487738063738248668731)
          ·
            refine ⟨824231607095607373003097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549487738063738248668731 824231607095607373003097)
            ·
              refine ⟨618173705321705529752323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824231607095607373003097 618173705321705529752323)
              ·
                refine ⟨927260557982558294628485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618173705321705529752323 927260557982558294628485)
                ·
                  refine ⟨173861354621729680242841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 927260557982558294628485 173861354621729680242841)
                  ·
                    rfl

theorem cell20_380918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_380918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380918 prefixEnd_380918 := by exact prefixLift 380918
  have htrace : WordTrace (prefixWord ++ tailWord_380918) baseStart_380918 baseEnd_380918 := by
    simpa [prefixWord, tailWord_380918, baseEnd_380918] using wordTrace_append hprefix tailTrace_380918
  have hstable : (prefixWord ++ tailWord_380918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380918).length < 2 ^ (prefixWord ++ tailWord_380918).sum := by decide
  have hdescent : baseEnd_380918 < baseStart_380918 := by decide
  rcases family_descends (prefixWord ++ tailWord_380918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380929 : List Nat := [1, 2, 4, 1, 2, 1, 2, 7]
def baseStart_380929 : Nat := 118140960795 + 380929 * 2 ^ 59
def prefixEnd_380929 : Nat := 4983230072969 + 3 ^ 40 * 380929 * 2
def baseEnd_380929 : Nat := 57955458440487510292043

theorem tailTrace_380929 : CollatzResearch.WordTrace tailWord_380929 prefixEnd_380929 57955458440487510292043 := by
  unfold tailWord_380929
  simp only [CollatzResearch.WordTrace]
  refine ⟨13893622036966765338817841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9262414691311176892545227 13893622036966765338817841)
  ·
    refine ⟨10420216527725074004113381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13893622036966765338817841 10420216527725074004113381)
    ·
      refine ⟨1953790598948451375771259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10420216527725074004113381 1953790598948451375771259)
      ·
        refine ⟨2930685898422677063656889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953790598948451375771259 2930685898422677063656889)
        ·
          refine ⟨2198014423817007797742667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2930685898422677063656889 2198014423817007797742667)
          ·
            refine ⟨3297021635725511696614001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198014423817007797742667 3297021635725511696614001)
            ·
              refine ⟨2472766226794133772460501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3297021635725511696614001 2472766226794133772460501)
              ·
                refine ⟨57955458440487510292043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2472766226794133772460501 57955458440487510292043)
                ·
                  rfl

theorem cell20_380929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_380929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380929 prefixEnd_380929 := by exact prefixLift 380929
  have htrace : WordTrace (prefixWord ++ tailWord_380929) baseStart_380929 baseEnd_380929 := by
    simpa [prefixWord, tailWord_380929, baseEnd_380929] using wordTrace_append hprefix tailTrace_380929
  have hstable : (prefixWord ++ tailWord_380929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380929).length < 2 ^ (prefixWord ++ tailWord_380929).sum := by decide
  have hdescent : baseEnd_380929 < baseStart_380929 := by decide
  rcases family_descends (prefixWord ++ tailWord_380929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380956 : List Nat := [2, 2, 3, 1, 3, 1, 3, 3, 2]
def baseStart_380956 : Nat := 118140960795 + 380956 * 2 ^ 59
def prefixEnd_380956 : Nat := 4983230072969 + 3 ^ 40 * 380956 * 2
def baseEnd_380956 : Nat := 173878698857170436976019

theorem tailTrace_380956 : CollatzResearch.WordTrace tailWord_380956 prefixEnd_380956 173878698857170436976019 := by
  unfold tailWord_380956
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947303403934474475025361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9263071205245965966700481 6947303403934474475025361)
  ·
    refine ⟨5210477552950855856269021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6947303403934474475025361 5210477552950855856269021)
    ·
      refine ⟨1953929082356570946100883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5210477552950855856269021 1953929082356570946100883)
      ·
        refine ⟨2930893623534856419151325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953929082356570946100883 2930893623534856419151325)
        ·
          refine ⟨1099085108825571157181747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2930893623534856419151325 1099085108825571157181747)
          ·
            refine ⟨1648627663238356735772621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099085108825571157181747 1648627663238356735772621)
            ·
              refine ⟨618235373714383775914733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1648627663238356735772621 618235373714383775914733)
              ·
                refine ⟨231838265142893915968025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618235373714383775914733 231838265142893915968025)
                ·
                  refine ⟨173878698857170436976019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231838265142893915968025 173878698857170436976019)
                  ·
                    rfl

theorem cell20_380956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_380956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380956 prefixEnd_380956 := by exact prefixLift 380956
  have htrace : WordTrace (prefixWord ++ tailWord_380956) baseStart_380956 baseEnd_380956 := by
    simpa [prefixWord, tailWord_380956, baseEnd_380956] using wordTrace_append hprefix tailTrace_380956
  have hstable : (prefixWord ++ tailWord_380956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380956).length < 2 ^ (prefixWord ++ tailWord_380956).sum := by decide
  have hdescent : baseEnd_380956 < baseStart_380956 := by decide
  rcases family_descends (prefixWord ++ tailWord_380956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380977 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 4]
def baseStart_380977 : Nat := 118140960795 + 380977 * 2 ^ 59
def prefixEnd_380977 : Nat := 4983230072969 + 3 ^ 40 * 380977 * 2
def baseEnd_380977 : Nat := 173888283829387697275933

theorem tailTrace_380977 : CollatzResearch.WordTrace tailWord_380977 prefixEnd_380977 173888283829387697275933 := by
  unfold tailWord_380977
  simp only [CollatzResearch.WordTrace]
  refine ⟨13895372740792869536565185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9263581827195246357710123 13895372740792869536565185)
  ·
    refine ⟨10421529555594652152423889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13895372740792869536565185 10421529555594652152423889)
    ·
      refine ⟨7816147166695989114317917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10421529555594652152423889 7816147166695989114317917)
      ·
        refine ⟨2931055187510995917869219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7816147166695989114317917 2931055187510995917869219)
        ·
          refine ⟨4396582781266493876803829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2931055187510995917869219 4396582781266493876803829)
          ·
            refine ⟨412179635743733800950359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4396582781266493876803829 412179635743733800950359)
            ·
              refine ⟨618269453615600701425539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412179635743733800950359 618269453615600701425539)
              ·
                refine ⟨927404180423401052138309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618269453615600701425539 927404180423401052138309)
                ·
                  refine ⟨173888283829387697275933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 927404180423401052138309 173888283829387697275933)
                  ·
                    rfl

theorem cell20_380977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_380977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380977 prefixEnd_380977 := by exact prefixLift 380977
  have htrace : WordTrace (prefixWord ++ tailWord_380977) baseStart_380977 baseEnd_380977 := by
    simpa [prefixWord, tailWord_380977, baseEnd_380977] using wordTrace_append hprefix tailTrace_380977
  have hstable : (prefixWord ++ tailWord_380977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380977).length < 2 ^ (prefixWord ++ tailWord_380977).sum := by decide
  have hdescent : baseEnd_380977 < baseStart_380977 := by decide
  rcases family_descends (prefixWord ++ tailWord_380977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380984 : List Nat := [2, 1, 2, 1, 6, 1, 2, 5]
def baseStart_380984 : Nat := 118140960795 + 380984 * 2 ^ 59
def prefixEnd_380984 : Nat := 4983230072969 + 3 ^ 40 * 380984 * 2
def baseEnd_380984 : Nat := 57963826273375594680857

theorem tailTrace_380984 : CollatzResearch.WordTrace tailWord_380984 prefixEnd_380984 57963826273375594680857 := by
  unfold tailWord_380984
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947814025883754866035003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9263752034511673154713337 6947814025883754866035003)
  ·
    refine ⟨10421721038825632299052505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6947814025883754866035003 10421721038825632299052505)
    ·
      refine ⟨7816290779119224224289379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10421721038825632299052505 7816290779119224224289379)
      ·
        refine ⟨11724436168678836336434069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7816290779119224224289379 11724436168678836336434069)
        ·
          refine ⟨549582945406820453270347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11724436168678836336434069 549582945406820453270347)
          ·
            refine ⟨824374418110230679905521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549582945406820453270347 824374418110230679905521)
            ·
              refine ⟨618280813582673009929141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824374418110230679905521 618280813582673009929141)
              ·
                refine ⟨57963826273375594680857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 618280813582673009929141 57963826273375594680857)
                ·
                  rfl

theorem cell20_380984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_380984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_380984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_380984 prefixEnd_380984 := by exact prefixLift 380984
  have htrace : WordTrace (prefixWord ++ tailWord_380984) baseStart_380984 baseEnd_380984 := by
    simpa [prefixWord, tailWord_380984, baseEnd_380984] using wordTrace_append hprefix tailTrace_380984
  have hstable : (prefixWord ++ tailWord_380984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380984).length < 2 ^ (prefixWord ++ tailWord_380984).sum := by decide
  have hdescent : baseEnd_380984 < baseStart_380984 := by decide
  rcases family_descends (prefixWord ++ tailWord_380984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381029 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 3]
def baseStart_381029 : Nat := 118140960795 + 381029 * 2 ^ 59
def prefixEnd_381029 : Nat := 4983230072969 + 3 ^ 40 * 381029 * 2
def baseEnd_381029 : Nat := 173912018046306627542387

theorem tailTrace_381029 : CollatzResearch.WordTrace tailWord_381029 prefixEnd_381029 173912018046306627542387 := by
  unfold tailWord_381029
  simp only [CollatzResearch.WordTrace]
  refine ⟨13897269336604482417458141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9264846224402988278305427 13897269336604482417458141)
  ·
    refine ⟨5211476001226680906546803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13897269336604482417458141 5211476001226680906546803)
    ·
      refine ⟨7817214001840021359820205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5211476001226680906546803 7817214001840021359820205)
      ·
        refine ⟨2931455250690008009932577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7817214001840021359820205 2931455250690008009932577)
        ·
          refine ⟨2198591438017506007449433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2931455250690008009932577 2198591438017506007449433)
          ·
            refine ⟨1648943578513129505587075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2198591438017506007449433 1648943578513129505587075)
            ·
              refine ⟨2473415367769694258380613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648943578513129505587075 2473415367769694258380613)
              ·
                refine ⟨463765381456817673446365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2473415367769694258380613 463765381456817673446365)
                ·
                  refine ⟨173912018046306627542387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463765381456817673446365 173912018046306627542387)
                  ·
                    rfl

theorem cell20_381029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_381029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381029 prefixEnd_381029 := by exact prefixLift 381029
  have htrace : WordTrace (prefixWord ++ tailWord_381029) baseStart_381029 baseEnd_381029 := by
    simpa [prefixWord, tailWord_381029, baseEnd_381029] using wordTrace_append hprefix tailTrace_381029
  have hstable : (prefixWord ++ tailWord_381029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381029).length < 2 ^ (prefixWord ++ tailWord_381029).sum := by decide
  have hdescent : baseEnd_381029 < baseStart_381029 := by decide
  rcases family_descends (prefixWord ++ tailWord_381029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381046 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_381046 : Nat := 118140960795 + 381046 * 2 ^ 59
def prefixEnd_381046 : Nat := 4983230072969 + 3 ^ 40 * 381046 * 2
def baseEnd_381046 : Nat := 173919777309530123975651

theorem tailTrace_381046 : CollatzResearch.WordTrace tailWord_381046 prefixEnd_381046 173919777309530123975651 := by
  unfold tailWord_381046
  simp only [CollatzResearch.WordTrace]
  refine ⟨868618086096430895051687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9265259585028596213884661 868618086096430895051687)
  ·
    refine ⟨1302927129144646342577531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 868618086096430895051687 1302927129144646342577531)
    ·
      refine ⟨1954390693716969513866297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302927129144646342577531 1954390693716969513866297)
      ·
        refine ⟨1465793020287727135399723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1954390693716969513866297 1465793020287727135399723)
        ·
          refine ⟨2198689530431590703099585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465793020287727135399723 2198689530431590703099585)
          ·
            refine ⟨1649017147823693027324689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2198689530431590703099585 1649017147823693027324689)
            ·
              refine ⟨1236762860867769770493517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1649017147823693027324689 1236762860867769770493517)
              ·
                refine ⟨463786072825413663935069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1236762860867769770493517 463786072825413663935069)
                ·
                  refine ⟨173919777309530123975651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463786072825413663935069 173919777309530123975651)
                  ·
                    rfl

theorem cell20_381046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_381046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381046 prefixEnd_381046 := by exact prefixLift 381046
  have htrace : WordTrace (prefixWord ++ tailWord_381046) baseStart_381046 baseEnd_381046 := by
    simpa [prefixWord, tailWord_381046, baseEnd_381046] using wordTrace_append hprefix tailTrace_381046
  have hstable : (prefixWord ++ tailWord_381046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381046).length < 2 ^ (prefixWord ++ tailWord_381046).sum := by decide
  have hdescent : baseEnd_381046 < baseStart_381046 := by decide
  rcases family_descends (prefixWord ++ tailWord_381046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381060 : List Nat := [2, 3, 2, 1, 2, 1, 5, 4]
def baseStart_381060 : Nat := 118140960795 + 381060 * 2 ^ 59
def prefixEnd_381060 : Nat := 4983230072969 + 3 ^ 40 * 381060 * 2
def baseEnd_381060 : Nat := 57975389097002765836309

theorem tailTrace_381060 : CollatzResearch.WordTrace tailWord_381060 prefixEnd_381060 57975389097002765836309 := by
  unfold tailWord_381060
  simp only [CollatzResearch.WordTrace]
  refine ⟨6949199999746087355918317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9265599999661449807891089 6949199999746087355918317)
  ·
    refine ⟨2605949999904782758469369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6949199999746087355918317 2605949999904782758469369)
    ·
      refine ⟨1954462499928587068852027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2605949999904782758469369 1954462499928587068852027)
      ·
        refine ⟨2931693749892880603278041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954462499928587068852027 2931693749892880603278041)
        ·
          refine ⟨2198770312419660452458531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2931693749892880603278041 2198770312419660452458531)
          ·
            refine ⟨3298155468629490678687797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198770312419660452458531 3298155468629490678687797)
            ·
              refine ⟨309202075184014751126981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3298155468629490678687797 309202075184014751126981)
              ·
                refine ⟨57975389097002765836309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 309202075184014751126981 57975389097002765836309)
                ·
                  rfl

theorem cell20_381060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_381060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381060 prefixEnd_381060 := by exact prefixLift 381060
  have htrace : WordTrace (prefixWord ++ tailWord_381060) baseStart_381060 baseEnd_381060 := by
    simpa [prefixWord, tailWord_381060, baseEnd_381060] using wordTrace_append hprefix tailTrace_381060
  have hstable : (prefixWord ++ tailWord_381060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381060).length < 2 ^ (prefixWord ++ tailWord_381060).sum := by decide
  have hdescent : baseEnd_381060 < baseStart_381060 := by decide
  rcases family_descends (prefixWord ++ tailWord_381060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381074 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_381074 : Nat := 118140960795 + 381074 * 2 ^ 59
def prefixEnd_381074 : Nat := 4983230072969 + 3 ^ 40 * 381074 * 2
def baseEnd_381074 : Nat := 173932557272486471042203

theorem tailTrace_381074 : CollatzResearch.WordTrace tailWord_381074 prefixEnd_381074 173932557272486471042203 := by
  unfold tailWord_381074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3474727655360363775711569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9265940414294303401897517 3474727655360363775711569)
  ·
    refine ⟨2606045741520272831783677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3474727655360363775711569 2606045741520272831783677)
    ·
      refine ⟨977267153070102311918879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2606045741520272831783677 977267153070102311918879)
      ·
        refine ⟨1465900729605153467878319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977267153070102311918879 1465900729605153467878319)
        ·
          refine ⟨2198851094407730201817479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465900729605153467878319 2198851094407730201817479)
          ·
            refine ⟨3298276641611595302726219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198851094407730201817479 3298276641611595302726219)
            ·
              refine ⟨4947414962417392954089329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298276641611595302726219 4947414962417392954089329)
              ·
                refine ⟨3710561221813044715566997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4947414962417392954089329 3710561221813044715566997)
                ·
                  refine ⟨173932557272486471042203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3710561221813044715566997 173932557272486471042203)
                  ·
                    rfl

theorem cell20_381074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_381074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381074 prefixEnd_381074 := by exact prefixLift 381074
  have htrace : WordTrace (prefixWord ++ tailWord_381074) baseStart_381074 baseEnd_381074 := by
    simpa [prefixWord, tailWord_381074, baseEnd_381074] using wordTrace_append hprefix tailTrace_381074
  have hstable : (prefixWord ++ tailWord_381074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381074).length < 2 ^ (prefixWord ++ tailWord_381074).sum := by decide
  have hdescent : baseEnd_381074 < baseStart_381074 := by decide
  rcases family_descends (prefixWord ++ tailWord_381074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381101 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 3]
def baseStart_381101 : Nat := 118140960795 + 381101 * 2 ^ 59
def prefixEnd_381101 : Nat := 4983230072969 + 3 ^ 40 * 381101 * 2
def baseEnd_381101 : Nat := 173944880808194377142093

theorem tailTrace_381101 : CollatzResearch.WordTrace tailWord_381101 prefixEnd_381101 173944880808194377142093 := by
  unfold tailWord_381101
  simp only [CollatzResearch.WordTrace]
  refine ⟨13899895392343638714079157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9266596928229092476052771 13899895392343638714079157)
  ·
    refine ⟨1303115193032216129444921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13899895392343638714079157 1303115193032216129444921)
    ·
      refine ⟨977336394774162097083691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1303115193032216129444921 977336394774162097083691)
      ·
        refine ⟨1466004592161243145625537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977336394774162097083691 1466004592161243145625537)
        ·
          refine ⟨1099503444120932359219153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1466004592161243145625537 1099503444120932359219153)
          ·
            refine ⟨824627583090699269414365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1099503444120932359219153 824627583090699269414365)
            ·
              refine ⟨309235343659012226030387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 824627583090699269414365 309235343659012226030387)
              ·
                refine ⟨463853015488518339045581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309235343659012226030387 463853015488518339045581)
                ·
                  refine ⟨173944880808194377142093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463853015488518339045581 173944880808194377142093)
                  ·
                    rfl

theorem cell20_381101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_381101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381101 prefixEnd_381101 := by exact prefixLift 381101
  have htrace : WordTrace (prefixWord ++ tailWord_381101) baseStart_381101 baseEnd_381101 := by
    simpa [prefixWord, tailWord_381101, baseEnd_381101] using wordTrace_append hprefix tailTrace_381101
  have hstable : (prefixWord ++ tailWord_381101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381101).length < 2 ^ (prefixWord ++ tailWord_381101).sum := by decide
  have hdescent : baseEnd_381101 < baseStart_381101 := by decide
  rcases family_descends (prefixWord ++ tailWord_381101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381142 : List Nat := [5, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_381142 : Nat := 118140960795 + 381142 * 2 ^ 59
def prefixEnd_381142 : Nat := 4983230072969 + 3 ^ 40 * 381142 * 2
def baseEnd_381142 : Nat := 173963594325380456775259

theorem tailTrace_381142 : CollatzResearch.WordTrace tailWord_381142 prefixEnd_381142 173963594325380456775259 := by
  unfold tailWord_381142
  simp only [CollatzResearch.WordTrace]
  refine ⟨868836924074693919770105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9267593856796735144214453 868836924074693919770105)
  ·
    refine ⟨651627693056020439827579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 868836924074693919770105 651627693056020439827579)
    ·
      refine ⟨977441539584030659741369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 651627693056020439827579 977441539584030659741369)
      ·
        refine ⟨733081154688022994806027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 977441539584030659741369 733081154688022994806027)
        ·
          refine ⟨1099621732032034492209041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733081154688022994806027 1099621732032034492209041)
          ·
            refine ⟨824716299024025869156781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1099621732032034492209041 824716299024025869156781)
            ·
              refine ⟨309268612134009700933793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 824716299024025869156781 309268612134009700933793)
              ·
                refine ⟨231951459100507275700345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309268612134009700933793 231951459100507275700345)
                ·
                  refine ⟨173963594325380456775259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231951459100507275700345 173963594325380456775259)
                  ·
                    rfl

theorem cell20_381142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_381142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381142 prefixEnd_381142 := by exact prefixLift 381142
  have htrace : WordTrace (prefixWord ++ tailWord_381142) baseStart_381142 baseEnd_381142 := by
    simpa [prefixWord, tailWord_381142, baseEnd_381142] using wordTrace_append hprefix tailTrace_381142
  have hstable : (prefixWord ++ tailWord_381142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381142).length < 2 ^ (prefixWord ++ tailWord_381142).sum := by decide
  have hdescent : baseEnd_381142 < baseStart_381142 := by decide
  rcases family_descends (prefixWord ++ tailWord_381142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381157 : List Nat := [1, 3, 1, 4, 2, 1, 1, 7]
def baseStart_381157 : Nat := 118140960795 + 381157 * 2 ^ 59
def prefixEnd_381157 : Nat := 4983230072969 + 3 ^ 40 * 381157 * 2
def baseEnd_381157 : Nat := 57990146911369023758399

theorem tailTrace_381157 : CollatzResearch.WordTrace tailWord_381157 prefixEnd_381157 57990146911369023758399 := by
  unfold tailWord_381157
  simp only [CollatzResearch.WordTrace]
  refine ⟨13901937880140760278117725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9267958586760506852078483 13901937880140760278117725)
  ·
    refine ⟨5213226705052785104294147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13901937880140760278117725 5213226705052785104294147)
    ·
      refine ⟨7819840057579177656441221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213226705052785104294147 7819840057579177656441221)
      ·
        refine ⟨1466220010796095810582729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7819840057579177656441221 1466220010796095810582729)
        ·
          refine ⟨1099665008097071857937047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1466220010796095810582729 1099665008097071857937047)
          ·
            refine ⟨1649497512145607786905571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099665008097071857937047 1649497512145607786905571)
            ·
              refine ⟨2474246268218411680358357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649497512145607786905571 2474246268218411680358357)
              ·
                refine ⟨57990146911369023758399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2474246268218411680358357 57990146911369023758399)
                ·
                  rfl

theorem cell20_381157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_381157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381157 prefixEnd_381157 := by exact prefixLift 381157
  have htrace : WordTrace (prefixWord ++ tailWord_381157) baseStart_381157 baseEnd_381157 := by
    simpa [prefixWord, tailWord_381157, baseEnd_381157] using wordTrace_append hprefix tailTrace_381157
  have hstable : (prefixWord ++ tailWord_381157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381157).length < 2 ^ (prefixWord ++ tailWord_381157).sum := by decide
  have hdescent : baseEnd_381157 < baseStart_381157 := by decide
  rcases family_descends (prefixWord ++ tailWord_381157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381160 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 3]
def baseStart_381160 : Nat := 118140960795 + 381160 * 2 ^ 59
def prefixEnd_381160 : Nat := 4983230072969 + 3 ^ 40 * 381160 * 2
def baseEnd_381160 : Nat := 173971810015852394175185

theorem tailTrace_381160 : CollatzResearch.WordTrace tailWord_381160 prefixEnd_381160 173971810015852394175185 := by
  unfold tailWord_381160
  simp only [CollatzResearch.WordTrace]
  refine ⟨6951023649564945895238467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9268031532753261193651289 6951023649564945895238467)
  ·
    refine ⟨10426535474347418842857701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6951023649564945895238467 10426535474347418842857701)
    ·
      refine ⟨1954975401440141033035819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10426535474347418842857701 1954975401440141033035819)
      ·
        refine ⟨2932463102160211549553729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954975401440141033035819 2932463102160211549553729)
        ·
          refine ⟨2199347326620158662165297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2932463102160211549553729 2199347326620158662165297)
          ·
            refine ⟨1649510494965118996623973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2199347326620158662165297 1649510494965118996623973)
            ·
              refine ⟨309283217805959811866995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1649510494965118996623973 309283217805959811866995)
              ·
                refine ⟨463924826708939717800493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309283217805959811866995 463924826708939717800493)
                ·
                  refine ⟨173971810015852394175185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463924826708939717800493 173971810015852394175185)
                  ·
                    rfl

theorem cell20_381160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_381160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381160 prefixEnd_381160 := by exact prefixLift 381160
  have htrace : WordTrace (prefixWord ++ tailWord_381160) baseStart_381160 baseEnd_381160 := by
    simpa [prefixWord, tailWord_381160, baseEnd_381160] using wordTrace_append hprefix tailTrace_381160
  have hstable : (prefixWord ++ tailWord_381160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381160).length < 2 ^ (prefixWord ++ tailWord_381160).sum := by decide
  have hdescent : baseEnd_381160 < baseStart_381160 := by decide
  rcases family_descends (prefixWord ++ tailWord_381160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381171 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_381171 : Nat := 118140960795 + 381171 * 2 ^ 59
def prefixEnd_381171 : Nat := 4983230072969 + 3 ^ 40 * 381171 * 2
def baseEnd_381171 : Nat := 173976830715585244808473

theorem tailTrace_381171 : CollatzResearch.WordTrace tailWord_381171 prefixEnd_381171 173976830715585244808473 := by
  unfold tailWord_381171
  simp only [CollatzResearch.WordTrace]
  refine ⟨13902448502090040669127367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9268299001393360446084911 13902448502090040669127367)
  ·
    refine ⟨20853672753135061003691051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13902448502090040669127367 20853672753135061003691051)
    ·
      refine ⟨31280509129702591505536577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20853672753135061003691051 31280509129702591505536577)
      ·
        refine ⟨23460381847276943629152433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31280509129702591505536577 23460381847276943629152433)
        ·
          refine ⟨17595286385457707721864325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23460381847276943629152433 17595286385457707721864325)
          ·
            refine ⟨3299116197273320197849561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17595286385457707721864325 3299116197273320197849561)
            ·
              refine ⟨2474337147954990148387171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3299116197273320197849561 2474337147954990148387171)
              ·
                refine ⟨3711505721932485222580757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2474337147954990148387171 3711505721932485222580757)
                ·
                  refine ⟨173976830715585244808473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3711505721932485222580757 173976830715585244808473)
                  ·
                    rfl

theorem cell20_381171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_381171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381171 prefixEnd_381171 := by exact prefixLift 381171
  have htrace : WordTrace (prefixWord ++ tailWord_381171) baseStart_381171 baseEnd_381171 := by
    simpa [prefixWord, tailWord_381171, baseEnd_381171] using wordTrace_append hprefix tailTrace_381171
  have hstable : (prefixWord ++ tailWord_381171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381171).length < 2 ^ (prefixWord ++ tailWord_381171).sum := by decide
  have hdescent : baseEnd_381171 < baseStart_381171 := by decide
  rcases family_descends (prefixWord ++ tailWord_381171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381247 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_381247 : Nat := 118140960795 + 381247 * 2 ^ 59
def prefixEnd_381247 : Nat := 4983230072969 + 3 ^ 40 * 381247 * 2
def baseEnd_381247 : Nat := 174011519186466758274829

theorem tailTrace_381247 : CollatzResearch.WordTrace tailWord_381247 prefixEnd_381247 174011519186466758274829 := by
  unfold tailWord_381247
  simp only [CollatzResearch.WordTrace]
  refine ⟨13905220449814705648893995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9270146966543137099262663 13905220449814705648893995)
  ·
    refine ⟨20857830674722058473340993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13905220449814705648893995 20857830674722058473340993)
    ·
      refine ⟨15643373006041543855005745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20857830674722058473340993 15643373006041543855005745)
      ·
        refine ⟨11732529754531157891254309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15643373006041543855005745 11732529754531157891254309)
        ·
          refine ⟨2199849328974592104610183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11732529754531157891254309 2199849328974592104610183)
          ·
            refine ⟨3299773993461888156915275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199849328974592104610183 3299773993461888156915275)
            ·
              refine ⟨4949660990192832235372913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299773993461888156915275 4949660990192832235372913)
              ·
                refine ⟨3712245742644624176529685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4949660990192832235372913 3712245742644624176529685)
                ·
                  refine ⟨174011519186466758274829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3712245742644624176529685 174011519186466758274829)
                  ·
                    rfl

theorem cell20_381247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_381247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381247 prefixEnd_381247 := by exact prefixLift 381247
  have htrace : WordTrace (prefixWord ++ tailWord_381247) baseStart_381247 baseEnd_381247 := by
    simpa [prefixWord, tailWord_381247, baseEnd_381247] using wordTrace_append hprefix tailTrace_381247
  have hstable : (prefixWord ++ tailWord_381247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381247).length < 2 ^ (prefixWord ++ tailWord_381247).sum := by decide
  have hdescent : baseEnd_381247 < baseStart_381247 := by decide
  rcases family_descends (prefixWord ++ tailWord_381247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381264 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_381264 : Nat := 118140960795 + 381264 * 2 ^ 59
def prefixEnd_381264 : Nat := 4983230072969 + 3 ^ 40 * 381264 * 2
def baseEnd_381264 : Nat := 174019278449690254708093

theorem tailTrace_381264 : CollatzResearch.WordTrace tailWord_381264 prefixEnd_381264 174019278449690254708093 := by
  unfold tailWord_381264
  simp only [CollatzResearch.WordTrace]
  refine ⟨6952920245376558776131423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9270560327168745034841897 6952920245376558776131423)
  ·
    refine ⟨10429380368064838164197135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6952920245376558776131423 10429380368064838164197135)
    ·
      refine ⟨15644070552097257246295703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10429380368064838164197135 15644070552097257246295703)
      ·
        refine ⟨23466105828145885869443555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15644070552097257246295703 23466105828145885869443555)
        ·
          refine ⟨35199158742218828804165333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23466105828145885869443555 35199158742218828804165333)
          ·
            refine ⟨824980283020753800097625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35199158742218828804165333 824980283020753800097625)
            ·
              refine ⟨618735212265565350073219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824980283020753800097625 618735212265565350073219)
              ·
                refine ⟨928102818398348025109829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618735212265565350073219 928102818398348025109829)
                ·
                  refine ⟨174019278449690254708093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 928102818398348025109829 174019278449690254708093)
                  ·
                    rfl

theorem cell20_381264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_381264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381264 prefixEnd_381264 := by exact prefixLift 381264
  have htrace : WordTrace (prefixWord ++ tailWord_381264) baseStart_381264 baseEnd_381264 := by
    simpa [prefixWord, tailWord_381264, baseEnd_381264] using wordTrace_append hprefix tailTrace_381264
  have hstable : (prefixWord ++ tailWord_381264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381264).length < 2 ^ (prefixWord ++ tailWord_381264).sum := by decide
  have hdescent : baseEnd_381264 < baseStart_381264 := by decide
  rcases family_descends (prefixWord ++ tailWord_381264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381288 : List Nat := [2, 1, 4, 2, 2, 1, 4, 4]
def baseStart_381288 : Nat := 118140960795 + 381288 * 2 ^ 59
def prefixEnd_381288 : Nat := 4983230072969 + 3 ^ 40 * 381288 * 2
def baseEnd_381288 : Nat := 58010077567884279302665

theorem tailTrace_381288 : CollatzResearch.WordTrace tailWord_381288 prefixEnd_381288 58010077567884279302665 := by
  unfold tailWord_381288
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953357921333084825568259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9271143895110779767424345 6953357921333084825568259)
  ·
    refine ⟨10430036881999627238352389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6953357921333084825568259 10430036881999627238352389)
    ·
      refine ⟨1955631915374930107191073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10430036881999627238352389 1955631915374930107191073)
      ·
        refine ⟨1466723936531197580393305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1955631915374930107191073 1466723936531197580393305)
        ·
          refine ⟨1100042952398398185294979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1466723936531197580393305 1100042952398398185294979)
          ·
            refine ⟨1650064428597597277942469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100042952398398185294979 1650064428597597277942469)
            ·
              refine ⟨309387080362049489614213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1650064428597597277942469 309387080362049489614213)
              ·
                refine ⟨58010077567884279302665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 309387080362049489614213 58010077567884279302665)
                ·
                  rfl

theorem cell20_381288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_381288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381288 prefixEnd_381288 := by exact prefixLift 381288
  have htrace : WordTrace (prefixWord ++ tailWord_381288) baseStart_381288 baseEnd_381288 := by
    simpa [prefixWord, tailWord_381288, baseEnd_381288] using wordTrace_append hprefix tailTrace_381288
  have hstable : (prefixWord ++ tailWord_381288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381288).length < 2 ^ (prefixWord ++ tailWord_381288).sum := by decide
  have hdescent : baseEnd_381288 < baseStart_381288 := by decide
  rcases family_descends (prefixWord ++ tailWord_381288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381298 : List Nat := [3, 2, 1, 2, 1, 5, 1, 3, 2]
def baseStart_381298 : Nat := 118140960795 + 381298 * 2 ^ 59
def prefixEnd_381298 : Nat := 4983230072969 + 3 ^ 40 * 381298 * 2
def baseEnd_381298 : Nat := 174034796976137247574621

theorem tailTrace_381298 : CollatzResearch.WordTrace tailWord_381298 prefixEnd_381298 174034796976137247574621 := by
  unfold tailWord_381298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3476770143157485339750137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9271387048419960906000365 3476770143157485339750137)
  ·
    refine ⟨2607577607368114004812603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3476770143157485339750137 2607577607368114004812603)
    ·
      refine ⟨3911366411052171007218905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2607577607368114004812603 3911366411052171007218905)
      ·
        refine ⟨2933524808289128255414179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3911366411052171007218905 2933524808289128255414179)
        ·
          refine ⟨4400287212433692383121269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2933524808289128255414179 4400287212433692383121269)
          ·
            refine ⟨412526926165658660917619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4400287212433692383121269 412526926165658660917619)
            ·
              refine ⟨618790389248487991376429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412526926165658660917619 618790389248487991376429)
              ·
                refine ⟨232046395968182996766161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618790389248487991376429 232046395968182996766161)
                ·
                  refine ⟨174034796976137247574621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232046395968182996766161 174034796976137247574621)
                  ·
                    rfl

theorem cell20_381298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_381298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381298 prefixEnd_381298 := by exact prefixLift 381298
  have htrace : WordTrace (prefixWord ++ tailWord_381298) baseStart_381298 baseEnd_381298 := by
    simpa [prefixWord, tailWord_381298, baseEnd_381298] using wordTrace_append hprefix tailTrace_381298
  have hstable : (prefixWord ++ tailWord_381298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381298).length < 2 ^ (prefixWord ++ tailWord_381298).sum := by decide
  have hdescent : baseEnd_381298 < baseStart_381298 := by decide
  rcases family_descends (prefixWord ++ tailWord_381298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381309 : List Nat := [1, 4, 1, 1, 2, 5, 6]
def baseStart_381309 : Nat := 118140960795 + 381309 * 2 ^ 59
def prefixEnd_381309 : Nat := 4983230072969 + 3 ^ 40 * 381309 * 2
def baseEnd_381309 : Nat := 19337757519541122023101

theorem tailTrace_381309 : CollatzResearch.WordTrace tailWord_381309 prefixEnd_381309 19337757519541122023101 := by
  unfold tailWord_381309
  simp only [CollatzResearch.WordTrace]
  refine ⟨13907481775590090237650981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9271654517060060158433987 13907481775590090237650981)
  ·
    refine ⟨2607652832923141919559559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13907481775590090237650981 2607652832923141919559559)
    ·
      refine ⟨3911479249384712879339339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2607652832923141919559559 3911479249384712879339339)
      ·
        refine ⟨5867218874077069319009009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911479249384712879339339 5867218874077069319009009)
        ·
          refine ⟨4400414155557801989256757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5867218874077069319009009 4400414155557801989256757)
          ·
            refine ⟨412538827083543936492821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4400414155557801989256757 412538827083543936492821)
            ·
              refine ⟨19337757519541122023101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 412538827083543936492821 19337757519541122023101)
              ·
                rfl

theorem cell20_381309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 6].length) (baseStart_381309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381309 prefixEnd_381309 := by exact prefixLift 381309
  have htrace : WordTrace (prefixWord ++ tailWord_381309) baseStart_381309 baseEnd_381309 := by
    simpa [prefixWord, tailWord_381309, baseEnd_381309] using wordTrace_append hprefix tailTrace_381309
  have hstable : (prefixWord ++ tailWord_381309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381309).length < 2 ^ (prefixWord ++ tailWord_381309).sum := by decide
  have hdescent : baseEnd_381309 < baseStart_381309 := by decide
  rcases family_descends (prefixWord ++ tailWord_381309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381316 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_381316 : Nat := 118140960795 + 381316 * 2 ^ 59
def prefixEnd_381316 : Nat := 4983230072969 + 3 ^ 40 * 381316 * 2
def baseEnd_381316 : Nat := 174043012666609184974547

theorem tailTrace_381316 : CollatzResearch.WordTrace tailWord_381316 prefixEnd_381316 174043012666609184974547 := by
  unfold tailWord_381316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953868543282365216577901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9271824724376486955437201 6953868543282365216577901)
  ·
    refine ⟨2607700703730886956216713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6953868543282365216577901 2607700703730886956216713)
    ·
      refine ⟨1955775527798165217162535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2607700703730886956216713 1955775527798165217162535)
      ·
        refine ⟨2933663291697247825743803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955775527798165217162535 2933663291697247825743803)
        ·
          refine ⟨4400494937545871738615705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2933663291697247825743803 4400494937545871738615705)
          ·
            refine ⟨3300371203159403803961779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4400494937545871738615705 3300371203159403803961779)
            ·
              refine ⟨4950556804739105705942669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300371203159403803961779 4950556804739105705942669)
              ·
                refine ⟨1856458801777164639728501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4950556804739105705942669 1856458801777164639728501)
                ·
                  refine ⟨174043012666609184974547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1856458801777164639728501 174043012666609184974547)
                  ·
                    rfl

theorem cell20_381316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_381316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381316 prefixEnd_381316 := by exact prefixLift 381316
  have htrace : WordTrace (prefixWord ++ tailWord_381316) baseStart_381316 baseEnd_381316 := by
    simpa [prefixWord, tailWord_381316, baseEnd_381316] using wordTrace_append hprefix tailTrace_381316
  have hstable : (prefixWord ++ tailWord_381316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381316).length < 2 ^ (prefixWord ++ tailWord_381316).sum := by decide
  have hdescent : baseEnd_381316 < baseStart_381316 := by decide
  rcases family_descends (prefixWord ++ tailWord_381316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381326 : List Nat := [4, 1, 1, 4, 1, 2, 2, 5]
def baseStart_381326 : Nat := 118140960795 + 381326 * 2 ^ 59
def prefixEnd_381326 : Nat := 4983230072969 + 3 ^ 40 * 381326 * 2
def baseEnd_381326 : Nat := 58015858979697864880391

theorem tailTrace_381326 : CollatzResearch.WordTrace tailWord_381326 prefixEnd_381326 58015858979697864880391 := by
  unfold tailWord_381326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1738512727066062767627479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9272067877685668094013221 1738512727066062767627479)
  ·
    refine ⟨2607769090599094151441219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1738512727066062767627479 2607769090599094151441219)
    ·
      refine ⟨3911653635898641227161829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2607769090599094151441219 3911653635898641227161829)
      ·
        refine ⟨733435056730995230092843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3911653635898641227161829 733435056730995230092843)
        ·
          refine ⟨1100152585096492845139265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733435056730995230092843 1100152585096492845139265)
          ·
            refine ⟨825114438822369633854449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100152585096492845139265 825114438822369633854449)
            ·
              refine ⟨618835829116777225390837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825114438822369633854449 618835829116777225390837)
              ·
                refine ⟨58015858979697864880391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 618835829116777225390837 58015858979697864880391)
                ·
                  rfl

theorem cell20_381326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_381326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381326 prefixEnd_381326 := by exact prefixLift 381326
  have htrace : WordTrace (prefixWord ++ tailWord_381326) baseStart_381326 baseEnd_381326 := by
    simpa [prefixWord, tailWord_381326, baseEnd_381326] using wordTrace_append hprefix tailTrace_381326
  have hstable : (prefixWord ++ tailWord_381326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381326).length < 2 ^ (prefixWord ++ tailWord_381326).sum := by decide
  have hdescent : baseEnd_381326 < baseStart_381326 := by decide
  rcases family_descends (prefixWord ++ tailWord_381326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381364 : List Nat := [2, 5, 2, 2, 9]
def baseStart_381364 : Nat := 118140960795 + 381364 * 2 ^ 59
def prefixEnd_381364 : Nat := 4983230072969 + 3 ^ 40 * 381364 * 2
def baseEnd_381364 : Nat := 2148949644130053720671

theorem tailTrace_381364 : CollatzResearch.WordTrace tailWord_381364 prefixEnd_381364 2148949644130053720671 := by
  unfold tailWord_381364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6954743895195417315451573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9272991860260556420602097 6954743895195417315451573)
  ·
    refine ⟨652007240174570373323585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6954743895195417315451573 652007240174570373323585)
    ·
      refine ⟨489005430130927779992689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 652007240174570373323585 489005430130927779992689)
      ·
        refine ⟨366754072598195834994517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489005430130927779992689 366754072598195834994517)
        ·
          refine ⟨2148949644130053720671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 366754072598195834994517 2148949644130053720671)
          ·
            rfl

theorem cell20_381364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 9].length) (baseStart_381364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381364 prefixEnd_381364 := by exact prefixLift 381364
  have htrace : WordTrace (prefixWord ++ tailWord_381364) baseStart_381364 baseEnd_381364 := by
    simpa [prefixWord, tailWord_381364, baseEnd_381364] using wordTrace_append hprefix tailTrace_381364
  have hstable : (prefixWord ++ tailWord_381364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381364).length < 2 ^ (prefixWord ++ tailWord_381364).sum := by decide
  have hdescent : baseEnd_381364 < baseStart_381364 := by decide
  rcases family_descends (prefixWord ++ tailWord_381364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381374 : List Nat := [4, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_381374 : Nat := 118140960795 + 381374 * 2 ^ 59
def prefixEnd_381374 : Nat := 4983230072969 + 3 ^ 40 * 381374 * 2
def baseEnd_381374 : Nat := 174069485447018761040977

theorem tailTrace_381374 : CollatzResearch.WordTrace tailWord_381374 prefixEnd_381374 174069485447018761040977 := by
  unfold tailWord_381374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1738731565044325792345897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9273235013569737559178117 1738731565044325792345897)
  ·
    refine ⟨1304048673783244344259423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1738731565044325792345897 1304048673783244344259423)
    ·
      refine ⟨1956073010674866516389135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1304048673783244344259423 1956073010674866516389135)
      ·
        refine ⟨2934109516012299774583703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1956073010674866516389135 2934109516012299774583703)
        ·
          refine ⟨4401164274018449661875555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934109516012299774583703 4401164274018449661875555)
          ·
            refine ⟨6601746411027674492813333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4401164274018449661875555 6601746411027674492813333)
            ·
              refine ⟨309456863016922241850625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6601746411027674492813333 309456863016922241850625)
              ·
                refine ⟨232092647262691681387969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309456863016922241850625 232092647262691681387969)
                ·
                  refine ⟨174069485447018761040977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232092647262691681387969 174069485447018761040977)
                  ·
                    rfl

theorem cell20_381374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_381374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381374 prefixEnd_381374 := by exact prefixLift 381374
  have htrace : WordTrace (prefixWord ++ tailWord_381374) baseStart_381374 baseEnd_381374 := by
    simpa [prefixWord, tailWord_381374, baseEnd_381374] using wordTrace_append hprefix tailTrace_381374
  have hstable : (prefixWord ++ tailWord_381374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381374).length < 2 ^ (prefixWord ++ tailWord_381374).sum := by decide
  have hdescent : baseEnd_381374 < baseStart_381374 := by decide
  rcases family_descends (prefixWord ++ tailWord_381374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381377 : List Nat := [1, 2, 7, 1, 2, 1, 1, 5]
def baseStart_381377 : Nat := 118140960795 + 381377 * 2 ^ 59
def prefixEnd_381377 : Nat := 4983230072969 + 3 ^ 40 * 381377 * 2
def baseEnd_381377 : Nat := 58023618242921361313655

theorem tailTrace_381377 : CollatzResearch.WordTrace tailWord_381377 prefixEnd_381377 58023618242921361313655 := by
  unfold tailWord_381377
  simp only [CollatzResearch.WordTrace]
  refine ⟨13909961939343737851126385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9273307959562491900750923 13909961939343737851126385)
  ·
    refine ⟨10432471454507803388344789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13909961939343737851126385 10432471454507803388344789)
    ·
      refine ⟨244511049715026641914331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10432471454507803388344789 244511049715026641914331)
      ·
        refine ⟨366766574572539962871497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244511049715026641914331 366766574572539962871497)
        ·
          refine ⟨275074930929404972153623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366766574572539962871497 275074930929404972153623)
          ·
            refine ⟨412612396394107458230435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275074930929404972153623 412612396394107458230435)
            ·
              refine ⟨618918594591161187345653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412612396394107458230435 618918594591161187345653)
              ·
                refine ⟨58023618242921361313655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 618918594591161187345653 58023618242921361313655)
                ·
                  rfl

theorem cell20_381377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 5].length) (baseStart_381377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381377 prefixEnd_381377 := by exact prefixLift 381377
  have htrace : WordTrace (prefixWord ++ tailWord_381377) baseStart_381377 baseEnd_381377 := by
    simpa [prefixWord, tailWord_381377, baseEnd_381377] using wordTrace_append hprefix tailTrace_381377
  have hstable : (prefixWord ++ tailWord_381377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381377).length < 2 ^ (prefixWord ++ tailWord_381377).sum := by decide
  have hdescent : baseEnd_381377 < baseStart_381377 := by decide
  rcases family_descends (prefixWord ++ tailWord_381377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381454 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_381454 : Nat := 118140960795 + 381454 * 2 ^ 59
def prefixEnd_381454 : Nat := 4983230072969 + 3 ^ 40 * 381454 * 2
def baseEnd_381454 : Nat := 174105999626894038373983

theorem tailTrace_381454 : CollatzResearch.WordTrace tailWord_381454 prefixEnd_381454 174105999626894038373983 := by
  unfold tailWord_381454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739096295008097500209927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9275180240043186667786277 1739096295008097500209927)
  ·
    refine ⟨2608644442512146250314891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1739096295008097500209927 2608644442512146250314891)
    ·
      refine ⟨3912966663768219375472337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2608644442512146250314891 3912966663768219375472337)
      ·
        refine ⟨2934724997826164531604253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3912966663768219375472337 2934724997826164531604253)
        ·
          refine ⟨1100521874184811699351595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2934724997826164531604253 1100521874184811699351595)
          ·
            refine ⟨1650782811277217549027393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100521874184811699351595 1650782811277217549027393)
            ·
              refine ⟨1238087108457913161770545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650782811277217549027393 1238087108457913161770545)
              ·
                refine ⟨928565331343434871327909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1238087108457913161770545 928565331343434871327909)
                ·
                  refine ⟨174105999626894038373983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 928565331343434871327909 174105999626894038373983)
                  ·
                    rfl

theorem cell20_381454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_381454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381454 prefixEnd_381454 := by exact prefixLift 381454
  have htrace : WordTrace (prefixWord ++ tailWord_381454) baseStart_381454 baseEnd_381454 := by
    simpa [prefixWord, tailWord_381454, baseEnd_381454] using wordTrace_append hprefix tailTrace_381454
  have hstable : (prefixWord ++ tailWord_381454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381454).length < 2 ^ (prefixWord ++ tailWord_381454).sum := by decide
  have hdescent : baseEnd_381454 < baseStart_381454 := by decide
  rcases family_descends (prefixWord ++ tailWord_381454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381468 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_381468 : Nat := 118140960795 + 381468 * 2 ^ 59
def prefixEnd_381468 : Nat := 4983230072969 + 3 ^ 40 * 381468 * 2
def baseEnd_381468 : Nat := 174112389608372211907259

theorem tailTrace_381468 : CollatzResearch.WordTrace tailWord_381468 prefixEnd_381468 174112389608372211907259 := by
  unfold tailWord_381468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6956640491007030196344529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9275520654676040261792705 6956640491007030196344529)
  ·
    refine ⟨5217480368255272647258397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6956640491007030196344529 5217480368255272647258397)
    ·
      refine ⟨1956555138095727242721899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5217480368255272647258397 1956555138095727242721899)
      ·
        refine ⟨2934832707143590864082849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1956555138095727242721899 2934832707143590864082849)
        ·
          refine ⟨2201124530357693148062137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2934832707143590864082849 2201124530357693148062137)
          ·
            refine ⟨1650843397768269861046603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2201124530357693148062137 1650843397768269861046603)
            ·
              refine ⟨2476265096652404791569905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650843397768269861046603 2476265096652404791569905)
              ·
                refine ⟨1857198822489303593677429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2476265096652404791569905 1857198822489303593677429)
                ·
                  refine ⟨174112389608372211907259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1857198822489303593677429 174112389608372211907259)
                  ·
                    rfl

theorem cell20_381468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_381468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381468 prefixEnd_381468 := by exact prefixLift 381468
  have htrace : WordTrace (prefixWord ++ tailWord_381468) baseStart_381468 baseEnd_381468 := by
    simpa [prefixWord, tailWord_381468, baseEnd_381468] using wordTrace_append hprefix tailTrace_381468
  have hstable : (prefixWord ++ tailWord_381468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381468).length < 2 ^ (prefixWord ++ tailWord_381468).sum := by decide
  have hdescent : baseEnd_381468 < baseStart_381468 := by decide
  rcases family_descends (prefixWord ++ tailWord_381468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381554 : List Nat := [3, 2, 1, 2, 4, 2, 1, 5]
def baseStart_381554 : Nat := 118140960795 + 381554 * 2 ^ 59
def prefixEnd_381554 : Nat := 4983230072969 + 3 ^ 40 * 381554 * 2
def baseEnd_381554 : Nat := 58050547450579378346747

theorem tailTrace_381554 : CollatzResearch.WordTrace tailWord_381554 prefixEnd_381554 58050547450579378346747 := by
  unfold tailWord_381554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479104414925624270079929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9277611773134998053546477 3479104414925624270079929)
  ·
    refine ⟨2609328311194218202559947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3479104414925624270079929 2609328311194218202559947)
    ·
      refine ⟨3913992466791327303839921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2609328311194218202559947 3913992466791327303839921)
      ·
        refine ⟨2935494350093495477879941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3913992466791327303839921 2935494350093495477879941)
        ·
          refine ⟨550405190642530402102489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2935494350093495477879941 550405190642530402102489)
          ·
            refine ⟨412803892981897801576867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550405190642530402102489 412803892981897801576867)
            ·
              refine ⟨619205839472846702365301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412803892981897801576867 619205839472846702365301)
              ·
                refine ⟨58050547450579378346747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 619205839472846702365301 58050547450579378346747)
                ·
                  rfl

theorem cell20_381554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_381554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381554 prefixEnd_381554 := by exact prefixLift 381554
  have htrace : WordTrace (prefixWord ++ tailWord_381554) baseStart_381554 baseEnd_381554 := by
    simpa [prefixWord, tailWord_381554, baseEnd_381554] using wordTrace_append hprefix tailTrace_381554
  have hstable : (prefixWord ++ tailWord_381554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381554).length < 2 ^ (prefixWord ++ tailWord_381554).sum := by decide
  have hdescent : baseEnd_381554 < baseStart_381554 := by decide
  rcases family_descends (prefixWord ++ tailWord_381554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381575 : List Nat := [1, 1, 4, 2, 1, 2, 5, 4]
def baseStart_381575 : Nat := 118140960795 + 381575 * 2 ^ 59
def prefixEnd_381575 : Nat := 4983230072969 + 3 ^ 40 * 381575 * 2
def baseEnd_381575 : Nat := 58053742441318465113385

theorem tailTrace_381575 : CollatzResearch.WordTrace tailWord_381575 prefixEnd_381575 58053742441318465113385 := by
  unfold tailWord_381575
  simp only [CollatzResearch.WordTrace]
  refine ⟨13917183592626417666834179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9278122395084278444556119 13917183592626417666834179)
  ·
    refine ⟨20875775388939626500251269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13917183592626417666834179 20875775388939626500251269)
    ·
      refine ⟨3914207885426179968797113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20875775388939626500251269 3914207885426179968797113)
      ·
        refine ⟨2935655914069634976597835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3914207885426179968797113 2935655914069634976597835)
        ·
          refine ⟨4403483871104452464896753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935655914069634976597835 4403483871104452464896753)
          ·
            refine ⟨3302612903328339348672565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4403483871104452464896753 3302612903328339348672565)
            ·
              refine ⟨309619959687031813938053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3302612903328339348672565 309619959687031813938053)
              ·
                refine ⟨58053742441318465113385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 309619959687031813938053 58053742441318465113385)
                ·
                  rfl

theorem cell20_381575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 4].length) (baseStart_381575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381575 prefixEnd_381575 := by exact prefixLift 381575
  have htrace : WordTrace (prefixWord ++ tailWord_381575) baseStart_381575 baseEnd_381575 := by
    simpa [prefixWord, tailWord_381575, baseEnd_381575] using wordTrace_append hprefix tailTrace_381575
  have hstable : (prefixWord ++ tailWord_381575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381575).length < 2 ^ (prefixWord ++ tailWord_381575).sum := by decide
  have hdescent : baseEnd_381575 < baseStart_381575 := by decide
  rcases family_descends (prefixWord ++ tailWord_381575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381582 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_381582 : Nat := 118140960795 + 381582 * 2 ^ 59
def prefixEnd_381582 : Nat := 4983230072969 + 3 ^ 40 * 381582 * 2
def baseEnd_381582 : Nat := 174164422314694482106793

theorem tailTrace_381582 : CollatzResearch.WordTrace tailWord_381582 prefixEnd_381582 174164422314694482106793 := by
  unfold tailWord_381582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739679862950132232792375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9278292602400705241559333 1739679862950132232792375)
  ·
    refine ⟨2609519794425198349188563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1739679862950132232792375 2609519794425198349188563)
    ·
      refine ⟨3914279691637797523782845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2609519794425198349188563 3914279691637797523782845)
      ·
        refine ⟨1467854884364174071418567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3914279691637797523782845 1467854884364174071418567)
        ·
          refine ⟨2201782326546261107127851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467854884364174071418567 2201782326546261107127851)
          ·
            refine ⟨3302673489819391660691777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201782326546261107127851 3302673489819391660691777)
            ·
              refine ⟨2477005117364543745518833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3302673489819391660691777 2477005117364543745518833)
              ·
                refine ⟨1857753838023407809139125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477005117364543745518833 1857753838023407809139125)
                ·
                  refine ⟨174164422314694482106793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1857753838023407809139125 174164422314694482106793)
                  ·
                    rfl

theorem cell20_381582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_381582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381582 prefixEnd_381582 := by exact prefixLift 381582
  have htrace : WordTrace (prefixWord ++ tailWord_381582) baseStart_381582 baseEnd_381582 := by
    simpa [prefixWord, tailWord_381582, baseEnd_381582] using wordTrace_append hprefix tailTrace_381582
  have hstable : (prefixWord ++ tailWord_381582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381582).length < 2 ^ (prefixWord ++ tailWord_381582).sum := by decide
  have hdescent : baseEnd_381582 < baseStart_381582 := by decide
  rcases family_descends (prefixWord ++ tailWord_381582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381658 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_381658 : Nat := 118140960795 + 381658 * 2 ^ 59
def prefixEnd_381658 : Nat := 4983230072969 + 3 ^ 40 * 381658 * 2
def baseEnd_381658 : Nat := 174199110785575995573149

theorem tailTrace_381658 : CollatzResearch.WordTrace tailWord_381658 prefixEnd_381658 174199110785575995573149 := by
  unfold tailWord_381658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3480052712831430710526407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9280140567550481894737085 3480052712831430710526407)
  ·
    refine ⟨5220079069247146065789611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3480052712831430710526407 5220079069247146065789611)
    ·
      refine ⟨7830118603870719098684417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5220079069247146065789611 7830118603870719098684417)
      ·
        refine ⟨5872588952903039324013313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7830118603870719098684417 5872588952903039324013313)
        ·
          refine ⟨4404441714677279493009985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5872588952903039324013313 4404441714677279493009985)
          ·
            refine ⟨3303331286007959619757489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4404441714677279493009985 3303331286007959619757489)
            ·
              refine ⟨2477498464505969714818117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3303331286007959619757489 2477498464505969714818117)
              ·
                refine ⟨464530962094869321528397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2477498464505969714818117 464530962094869321528397)
                ·
                  refine ⟨174199110785575995573149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464530962094869321528397 174199110785575995573149)
                  ·
                    rfl

theorem cell20_381658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_381658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381658 prefixEnd_381658 := by exact prefixLift 381658
  have htrace : WordTrace (prefixWord ++ tailWord_381658) baseStart_381658 baseEnd_381658 := by
    simpa [prefixWord, tailWord_381658, baseEnd_381658] using wordTrace_append hprefix tailTrace_381658
  have hstable : (prefixWord ++ tailWord_381658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381658).length < 2 ^ (prefixWord ++ tailWord_381658).sum := by decide
  have hdescent : baseEnd_381658 < baseStart_381658 := by decide
  rcases family_descends (prefixWord ++ tailWord_381658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381727 : List Nat := [1, 1, 2, 4, 2, 4, 1, 5]
def baseStart_381727 : Nat := 118140960795 + 381727 * 2 ^ 59
def prefixEnd_381727 : Nat := 4983230072969 + 3 ^ 40 * 381727 * 2
def baseEnd_381727 : Nat := 58076868088572807424289

theorem tailTrace_381727 : CollatzResearch.WordTrace tailWord_381727 prefixEnd_381727 58076868088572807424289 := by
  unfold tailWord_381727
  simp only [CollatzResearch.WordTrace]
  refine ⟨13922727488075747626367435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9281818325383831750911623 13922727488075747626367435)
  ·
    refine ⟨20884091232113621439551153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13922727488075747626367435 20884091232113621439551153)
    ·
      refine ⟨15663068424085216079663365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20884091232113621439551153 15663068424085216079663365)
      ·
        refine ⟨2936825329515978014936881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15663068424085216079663365 2936825329515978014936881)
        ·
          refine ⟨2202618997136983511202661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2936825329515978014936881 2202618997136983511202661)
          ·
            refine ⟨412991061963184408350499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2202618997136983511202661 412991061963184408350499)
            ·
              refine ⟨619486592944776612525749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412991061963184408350499 619486592944776612525749)
              ·
                refine ⟨58076868088572807424289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 619486592944776612525749 58076868088572807424289)
                ·
                  rfl

theorem cell20_381727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 5].length) (baseStart_381727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381727 prefixEnd_381727 := by exact prefixLift 381727
  have htrace : WordTrace (prefixWord ++ tailWord_381727) baseStart_381727 baseEnd_381727 := by
    simpa [prefixWord, tailWord_381727, baseEnd_381727] using wordTrace_append hprefix tailTrace_381727
  have hstable : (prefixWord ++ tailWord_381727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381727).length < 2 ^ (prefixWord ++ tailWord_381727).sum := by decide
  have hdescent : baseEnd_381727 < baseStart_381727 := by decide
  rcases family_descends (prefixWord ++ tailWord_381727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381764 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 3]
def baseStart_381764 : Nat := 118140960795 + 381764 * 2 ^ 59
def prefixEnd_381764 : Nat := 4983230072969 + 3 ^ 40 * 381764 * 2
def baseEnd_381764 : Nat := 174247492073910738039383

theorem tailTrace_381764 : CollatzResearch.WordTrace tailWord_381764 prefixEnd_381764 174247492073910738039383 := by
  unfold tailWord_381764
  simp only [CollatzResearch.WordTrace]
  refine ⟨6962038494470851472732173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9282717992627801963642897 6962038494470851472732173)
  ·
    refine ⟨2610764435426569302274565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6962038494470851472732173 2610764435426569302274565)
    ·
      refine ⟨489518331642481744176481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2610764435426569302274565 489518331642481744176481)
      ·
        refine ⟨367138748731861308132361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489518331642481744176481 367138748731861308132361)
        ·
          refine ⟨275354061548895981099271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367138748731861308132361 275354061548895981099271)
          ·
            refine ⟨413031092323343971648907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275354061548895981099271 413031092323343971648907)
            ·
              refine ⟨619546638485015957473361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413031092323343971648907 619546638485015957473361)
              ·
                refine ⟨464659978863761968105021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619546638485015957473361 464659978863761968105021)
                ·
                  refine ⟨174247492073910738039383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464659978863761968105021 174247492073910738039383)
                  ·
                    rfl

theorem cell20_381764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_381764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381764 prefixEnd_381764 := by exact prefixLift 381764
  have htrace : WordTrace (prefixWord ++ tailWord_381764) baseStart_381764 baseEnd_381764 := by
    simpa [prefixWord, tailWord_381764, baseEnd_381764] using wordTrace_append hprefix tailTrace_381764
  have hstable : (prefixWord ++ tailWord_381764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381764).length < 2 ^ (prefixWord ++ tailWord_381764).sum := by decide
  have hdescent : baseEnd_381764 < baseStart_381764 := by decide
  rcases family_descends (prefixWord ++ tailWord_381764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381772 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_381772 : Nat := 118140960795 + 381772 * 2 ^ 59
def prefixEnd_381772 : Nat := 4983230072969 + 3 ^ 40 * 381772 * 2
def baseEnd_381772 : Nat := 174251143491898265772683

theorem tailTrace_381772 : CollatzResearch.WordTrace tailWord_381772 prefixEnd_381772 174251143491898265772683 := by
  unfold tailWord_381772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6962184386456360155877785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9282912515275146874503713 6962184386456360155877785)
  ·
    refine ⟨5221638289842270116908339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6962184386456360155877785 5221638289842270116908339)
    ·
      refine ⟨7832457434763405175362509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5221638289842270116908339 7832457434763405175362509)
      ·
        refine ⟨2937171538036276940760941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7832457434763405175362509 2937171538036276940760941)
        ·
          refine ⟨1101439326763603852785353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2937171538036276940760941 1101439326763603852785353)
          ·
            refine ⟨826079495072702889589015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1101439326763603852785353 826079495072702889589015)
            ·
              refine ⟨1239119242609054334383523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826079495072702889589015 1239119242609054334383523)
              ·
                refine ⟨1858678863913581501575285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239119242609054334383523 1858678863913581501575285)
                ·
                  refine ⟨174251143491898265772683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1858678863913581501575285 174251143491898265772683)
                  ·
                    rfl

theorem cell20_381772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_381772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381772 prefixEnd_381772 := by exact prefixLift 381772
  have htrace : WordTrace (prefixWord ++ tailWord_381772) baseStart_381772 baseEnd_381772 := by
    simpa [prefixWord, tailWord_381772, baseEnd_381772] using wordTrace_append hprefix tailTrace_381772
  have hstable : (prefixWord ++ tailWord_381772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381772).length < 2 ^ (prefixWord ++ tailWord_381772).sum := by decide
  have hdescent : baseEnd_381772 < baseStart_381772 := by decide
  rcases family_descends (prefixWord ++ tailWord_381772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381813 : List Nat := [1, 3, 4, 1, 1, 2, 3, 3, 2]
def baseStart_381813 : Nat := 118140960795 + 381813 * 2 ^ 59
def prefixEnd_381813 : Nat := 4983230072969 + 3 ^ 40 * 381813 * 2
def baseEnd_381813 : Nat := 174269857009084345405849

theorem tailTrace_381813 : CollatzResearch.WordTrace tailWord_381813 prefixEnd_381813 174269857009084345405849 := by
  unfold tailWord_381813
  simp only [CollatzResearch.WordTrace]
  refine ⟨13925864165764184313998093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9283909443842789542665395 13925864165764184313998093)
  ·
    refine ⟨5222199062161569117749285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13925864165764184313998093 5222199062161569117749285)
    ·
      refine ⟨979162324155294209577991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5222199062161569117749285 979162324155294209577991)
      ·
        refine ⟨1468743486232941314366987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979162324155294209577991 1468743486232941314366987)
        ·
          refine ⟨2203115229349411971550481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468743486232941314366987 2203115229349411971550481)
          ·
            refine ⟨1652336422012058978662861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2203115229349411971550481 1652336422012058978662861)
            ·
              refine ⟨619626158254522116998573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1652336422012058978662861 619626158254522116998573)
              ·
                refine ⟨232359809345445793874465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 619626158254522116998573 232359809345445793874465)
                ·
                  refine ⟨174269857009084345405849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232359809345445793874465 174269857009084345405849)
                  ·
                    rfl

theorem cell20_381813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_381813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381813 prefixEnd_381813 := by exact prefixLift 381813
  have htrace : WordTrace (prefixWord ++ tailWord_381813) baseStart_381813 baseEnd_381813 := by
    simpa [prefixWord, tailWord_381813, baseEnd_381813] using wordTrace_append hprefix tailTrace_381813
  have hstable : (prefixWord ++ tailWord_381813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381813).length < 2 ^ (prefixWord ++ tailWord_381813).sum := by decide
  have hdescent : baseEnd_381813 < baseStart_381813 := by decide
  rcases family_descends (prefixWord ++ tailWord_381813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381826 : List Nat := [3, 4, 2, 2, 1, 1, 3, 2, 2]
def baseStart_381826 : Nat := 118140960795 + 381826 * 2 ^ 59
def prefixEnd_381826 : Nat := 4983230072969 + 3 ^ 40 * 381826 * 2
def baseEnd_381826 : Nat := 174275790563314077972463

theorem tailTrace_381826 : CollatzResearch.WordTrace tailWord_381826 prefixEnd_381826 174275790563314077972463 := by
  unfold tailWord_381826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481584578679271883555333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9284225543144725022814221 3481584578679271883555333)
  ·
    refine ⟨652797108502363478166625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3481584578679271883555333 652797108502363478166625)
    ·
      refine ⟨489597831376772608624969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 652797108502363478166625 489597831376772608624969)
      ·
        refine ⟨367198373532579456468727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489597831376772608624969 367198373532579456468727)
        ·
          refine ⟨550797560298869184703091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367198373532579456468727 550797560298869184703091)
          ·
            refine ⟨826196340448303777054637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550797560298869184703091 826196340448303777054637)
            ·
              refine ⟨309823627668113916395489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 826196340448303777054637 309823627668113916395489)
              ·
                refine ⟨232367720751085437296617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309823627668113916395489 232367720751085437296617)
                ·
                  refine ⟨174275790563314077972463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232367720751085437296617 174275790563314077972463)
                  ·
                    rfl

theorem cell20_381826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_381826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381826 prefixEnd_381826 := by exact prefixLift 381826
  have htrace : WordTrace (prefixWord ++ tailWord_381826) baseStart_381826 baseEnd_381826 := by
    simpa [prefixWord, tailWord_381826, baseEnd_381826] using wordTrace_append hprefix tailTrace_381826
  have hstable : (prefixWord ++ tailWord_381826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381826).length < 2 ^ (prefixWord ++ tailWord_381826).sum := by decide
  have hdescent : baseEnd_381826 < baseStart_381826 := by decide
  rcases family_descends (prefixWord ++ tailWord_381826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381834 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_381834 : Nat := 118140960795 + 381834 * 2 ^ 59
def prefixEnd_381834 : Nat := 4983230072969 + 3 ^ 40 * 381834 * 2
def baseEnd_381834 : Nat := 174279441981301605705763

theorem tailTrace_381834 : CollatzResearch.WordTrace tailWord_381834 prefixEnd_381834 174279441981301605705763 := by
  unfold tailWord_381834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481657524672026225128139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9284420065792069933675037 3481657524672026225128139)
  ·
    refine ⟨5222486287008039337692209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3481657524672026225128139 5222486287008039337692209)
    ·
      refine ⟨3916864715256029503269157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5222486287008039337692209 3916864715256029503269157)
      ·
        refine ⟨734412134110505531862967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3916864715256029503269157 734412134110505531862967)
        ·
          refine ⟨1101618201165758297794451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734412134110505531862967 1101618201165758297794451)
          ·
            refine ⟨1652427301748637446691677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101618201165758297794451 1652427301748637446691677)
            ·
              refine ⟨619660238155739042509379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1652427301748637446691677 619660238155739042509379)
              ·
                refine ⟨929490357233608563764069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619660238155739042509379 929490357233608563764069)
                ·
                  refine ⟨174279441981301605705763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 929490357233608563764069 174279441981301605705763)
                  ·
                    rfl

theorem cell20_381834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_381834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381834 prefixEnd_381834 := by exact prefixLift 381834
  have htrace : WordTrace (prefixWord ++ tailWord_381834) baseStart_381834 baseEnd_381834 := by
    simpa [prefixWord, tailWord_381834, baseEnd_381834] using wordTrace_append hprefix tailTrace_381834
  have hstable : (prefixWord ++ tailWord_381834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381834).length < 2 ^ (prefixWord ++ tailWord_381834).sum := by decide
  have hdescent : baseEnd_381834 < baseStart_381834 := by decide
  rcases family_descends (prefixWord ++ tailWord_381834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381878 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_381878 : Nat := 118140960795 + 381878 * 2 ^ 59
def prefixEnd_381878 : Nat := 4983230072969 + 3 ^ 40 * 381878 * 2
def baseEnd_381878 : Nat := 174299524780233008238917

theorem tailTrace_381878 : CollatzResearch.WordTrace tailWord_381878 prefixEnd_381878 174299524780233008238917 := by
  unfold tailWord_381878
  simp only [CollatzResearch.WordTrace]
  refine ⟨870514681908043775944643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9285489940352466943409525 870514681908043775944643)
  ·
    refine ⟨1305772022862065663916965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 870514681908043775944643 1305772022862065663916965)
    ·
      refine ⟨244832254286637311984431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1305772022862065663916965 244832254286637311984431)
      ·
        refine ⟨367248381429955967976647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244832254286637311984431 367248381429955967976647)
        ·
          refine ⟨550872572144933951964971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367248381429955967976647 550872572144933951964971)
          ·
            refine ⟨826308858217400927947457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550872572144933951964971 826308858217400927947457)
            ·
              refine ⟨619731643663050695960593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826308858217400927947457 619731643663050695960593)
              ·
                refine ⟨464798732747288021970445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619731643663050695960593 464798732747288021970445)
                ·
                  refine ⟨174299524780233008238917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464798732747288021970445 174299524780233008238917)
                  ·
                    rfl

theorem cell20_381878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_381878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381878 prefixEnd_381878 := by exact prefixLift 381878
  have htrace : WordTrace (prefixWord ++ tailWord_381878) baseStart_381878 baseEnd_381878 := by
    simpa [prefixWord, tailWord_381878, baseEnd_381878] using wordTrace_append hprefix tailTrace_381878
  have hstable : (prefixWord ++ tailWord_381878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381878).length < 2 ^ (prefixWord ++ tailWord_381878).sum := by decide
  have hdescent : baseEnd_381878 < baseStart_381878 := by decide
  rcases family_descends (prefixWord ++ tailWord_381878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381885 : List Nat := [1, 4, 1, 2, 5, 1, 2, 2, 2]
def baseStart_381885 : Nat := 118140960795 + 381885 * 2 ^ 59
def prefixEnd_381885 : Nat := 4983230072969 + 3 ^ 40 * 381885 * 2
def baseEnd_381885 : Nat := 174302719770972095005555

theorem tailTrace_381885 : CollatzResearch.WordTrace tailWord_381885 prefixEnd_381885 174302719770972095005555 := by
  unfold tailWord_381885
  simp only [CollatzResearch.WordTrace]
  refine ⟨13928490221503340610619109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9285660147668893740412739 13928490221503340610619109)
  ·
    refine ⟨2611591916531876364491083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13928490221503340610619109 2611591916531876364491083)
    ·
      refine ⟨3917387874797814546736625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2611591916531876364491083 3917387874797814546736625)
      ·
        refine ⟨2938040906098360910052469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3917387874797814546736625 2938040906098360910052469)
        ·
          refine ⟨275441334946721335317419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2938040906098360910052469 275441334946721335317419)
          ·
            refine ⟨413162002420082002976129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275441334946721335317419 413162002420082002976129)
            ·
              refine ⟨309871501815061502232097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413162002420082002976129 309871501815061502232097)
              ·
                refine ⟨232403626361296126674073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309871501815061502232097 232403626361296126674073)
                ·
                  refine ⟨174302719770972095005555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232403626361296126674073 174302719770972095005555)
                  ·
                    rfl

theorem cell20_381885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_381885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381885 prefixEnd_381885 := by exact prefixLift 381885
  have htrace : WordTrace (prefixWord ++ tailWord_381885) baseStart_381885 baseEnd_381885 := by
    simpa [prefixWord, tailWord_381885, baseEnd_381885] using wordTrace_append hprefix tailTrace_381885
  have hstable : (prefixWord ++ tailWord_381885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381885).length < 2 ^ (prefixWord ++ tailWord_381885).sum := by decide
  have hdescent : baseEnd_381885 < baseStart_381885 := by decide
  rcases family_descends (prefixWord ++ tailWord_381885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381896 : List Nat := [2, 1, 3, 1, 6, 1, 1, 5]
def baseStart_381896 : Nat := 118140960795 + 381896 * 2 ^ 59
def prefixEnd_381896 : Nat := 4983230072969 + 3 ^ 40 * 381896 * 2
def baseEnd_381896 : Nat := 58102580156901648546281

theorem tailTrace_381896 : CollatzResearch.WordTrace tailWord_381896 prefixEnd_381896 58102580156901648546281 := by
  unfold tailWord_381896
  simp only [CollatzResearch.WordTrace]
  refine ⟨6964445712231744744634771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9285927616308992992846361 6964445712231744744634771)
  ·
    refine ⟨10446668568347617116952157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6964445712231744744634771 10446668568347617116952157)
    ·
      refine ⟨3917500713130356418857059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10446668568347617116952157 3917500713130356418857059)
      ·
        refine ⟨5876251069695534628285589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3917500713130356418857059 5876251069695534628285589)
        ·
          refine ⟨275449268891978185700887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5876251069695534628285589 275449268891978185700887)
          ·
            refine ⟨413173903337967278551331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275449268891978185700887 413173903337967278551331)
            ·
              refine ⟨619760855006950917826997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413173903337967278551331 619760855006950917826997)
              ·
                refine ⟨58102580156901648546281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 619760855006950917826997 58102580156901648546281)
                ·
                  rfl

theorem cell20_381896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_381896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381896 prefixEnd_381896 := by exact prefixLift 381896
  have htrace : WordTrace (prefixWord ++ tailWord_381896) baseStart_381896 baseEnd_381896 := by
    simpa [prefixWord, tailWord_381896, baseEnd_381896] using wordTrace_append hprefix tailTrace_381896
  have hstable : (prefixWord ++ tailWord_381896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381896).length < 2 ^ (prefixWord ++ tailWord_381896).sum := by decide
  have hdescent : baseEnd_381896 < baseStart_381896 := by decide
  rcases family_descends (prefixWord ++ tailWord_381896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381910 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_381910 : Nat := 118140960795 + 381910 * 2 ^ 59
def prefixEnd_381910 : Nat := 4983230072969 + 3 ^ 40 * 381910 * 2
def baseEnd_381910 : Nat := 174314130452183119172119

theorem tailTrace_381910 : CollatzResearch.WordTrace tailWord_381910 prefixEnd_381910 174314130452183119172119 := by
  unfold tailWord_381910
  simp only [CollatzResearch.WordTrace]
  refine ⟨870587627900798117517449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9286268030941846586852789 870587627900798117517449)
  ·
    refine ⟨652940720925598588138087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 870587627900798117517449 652940720925598588138087)
    ·
      refine ⟨979411081388397882207131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652940720925598588138087 979411081388397882207131)
      ·
        refine ⟨1469116622082596823310697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979411081388397882207131 1469116622082596823310697)
        ·
          refine ⟨1101837466561947617483023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1469116622082596823310697 1101837466561947617483023)
          ·
            refine ⟨1652756199842921426224535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101837466561947617483023 1652756199842921426224535)
            ·
              refine ⟨2479134299764382139336803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652756199842921426224535 2479134299764382139336803)
              ·
                refine ⟨3718701449646573209005205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479134299764382139336803 3718701449646573209005205)
                ·
                  refine ⟨174314130452183119172119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3718701449646573209005205 174314130452183119172119)
                  ·
                    rfl

theorem cell20_381910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_381910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381910 prefixEnd_381910 := by exact prefixLift 381910
  have htrace : WordTrace (prefixWord ++ tailWord_381910) baseStart_381910 baseEnd_381910 := by
    simpa [prefixWord, tailWord_381910, baseEnd_381910] using wordTrace_append hprefix tailTrace_381910
  have hstable : (prefixWord ++ tailWord_381910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381910).length < 2 ^ (prefixWord ++ tailWord_381910).sum := by decide
  have hdescent : baseEnd_381910 < baseStart_381910 := by decide
  rcases family_descends (prefixWord ++ tailWord_381910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381927 : List Nat := [1, 1, 5, 2, 2, 2, 2, 3, 2]
def baseStart_381927 : Nat := 118140960795 + 381927 * 2 ^ 59
def prefixEnd_381927 : Nat := 4983230072969 + 3 ^ 40 * 381927 * 2
def baseEnd_381927 : Nat := 174321889715406615605383

theorem tailTrace_381927 : CollatzResearch.WordTrace tailWord_381927 prefixEnd_381927 174321889715406615605383 := by
  unfold tailWord_381927
  simp only [CollatzResearch.WordTrace]
  refine ⟨13930022087351181783648035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9286681391567454522432023 13930022087351181783648035)
  ·
    refine ⟨20895033131026772675472053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13930022087351181783648035 20895033131026772675472053)
    ·
      refine ⟨1958909356033759938325505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20895033131026772675472053 1958909356033759938325505)
      ·
        refine ⟨1469182017025319953744129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1958909356033759938325505 1469182017025319953744129)
        ·
          refine ⟨1101886512768989965308097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1469182017025319953744129 1101886512768989965308097)
          ·
            refine ⟨826414884576742473981073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1101886512768989965308097 826414884576742473981073)
            ·
              refine ⟨619811163432556855485805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826414884576742473981073 619811163432556855485805)
              ·
                refine ⟨232429186287208820807177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 619811163432556855485805 232429186287208820807177)
                ·
                  refine ⟨174321889715406615605383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232429186287208820807177 174321889715406615605383)
                  ·
                    rfl

theorem cell20_381927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 2].length) (baseStart_381927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381927 prefixEnd_381927 := by exact prefixLift 381927
  have htrace : WordTrace (prefixWord ++ tailWord_381927) baseStart_381927 baseEnd_381927 := by
    simpa [prefixWord, tailWord_381927, baseEnd_381927] using wordTrace_append hprefix tailTrace_381927
  have hstable : (prefixWord ++ tailWord_381927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381927).length < 2 ^ (prefixWord ++ tailWord_381927).sum := by decide
  have hdescent : baseEnd_381927 < baseStart_381927 := by decide
  rcases family_descends (prefixWord ++ tailWord_381927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381945 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_381945 : Nat := 118140960795 + 381945 * 2 ^ 59
def prefixEnd_381945 : Nat := 4983230072969 + 3 ^ 40 * 381945 * 2
def baseEnd_381945 : Nat := 174330105405878553005309

theorem tailTrace_381945 : CollatzResearch.WordTrace tailWord_381945 prefixEnd_381945 174330105405878553005309 := by
  unfold tailWord_381945
  simp only [CollatzResearch.WordTrace]
  refine ⟨13930678601285970857803289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9287119067523980571868859 13930678601285970857803289)
  ·
    refine ⟨10448008950964478143352467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13930678601285970857803289 10448008950964478143352467)
    ·
      refine ⟨15672013426446717215028701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10448008950964478143352467 15672013426446717215028701)
      ·
        refine ⟨5877005034917518955635763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15672013426446717215028701 5877005034917518955635763)
        ·
          refine ⟨8815507552376278433453645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877005034917518955635763 8815507552376278433453645)
          ·
            refine ⟨3305815332141104412545117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8815507552376278433453645 3305815332141104412545117)
            ·
              refine ⟨1239680749552914154704419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3305815332141104412545117 1239680749552914154704419)
              ·
                refine ⟨1859521124329371232056629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239680749552914154704419 1859521124329371232056629)
                ·
                  refine ⟨174330105405878553005309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1859521124329371232056629 174330105405878553005309)
                  ·
                    rfl

theorem cell20_381945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_381945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381945 prefixEnd_381945 := by exact prefixLift 381945
  have htrace : WordTrace (prefixWord ++ tailWord_381945) baseStart_381945 baseEnd_381945 := by
    simpa [prefixWord, tailWord_381945, baseEnd_381945] using wordTrace_append hprefix tailTrace_381945
  have hstable : (prefixWord ++ tailWord_381945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381945).length < 2 ^ (prefixWord ++ tailWord_381945).sum := by decide
  have hdescent : baseEnd_381945 < baseStart_381945 := by decide
  rcases family_descends (prefixWord ++ tailWord_381945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381948 : List Nat := [2, 2, 2, 1, 2, 3, 2, 4, 2]
def baseStart_381948 : Nat := 118140960795 + 381948 * 2 ^ 59
def prefixEnd_381948 : Nat := 4983230072969 + 3 ^ 40 * 381948 * 2
def baseEnd_381948 : Nat := 174331474687623875905297

theorem tailTrace_381948 : CollatzResearch.WordTrace tailWord_381948 prefixEnd_381948 174331474687623875905297 := by
  unfold tailWord_381948
  simp only [CollatzResearch.WordTrace]
  refine ⟨6965394010137551185081249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9287192013516734913441665 6965394010137551185081249)
  ·
    refine ⟨5224045507603163388810937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6965394010137551185081249 5224045507603163388810937)
    ·
      refine ⟨3918034130702372541608203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5224045507603163388810937 3918034130702372541608203)
      ·
        refine ⟨5877051196053558812412305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918034130702372541608203 5877051196053558812412305)
        ·
          refine ⟨4407788397040169109309229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5877051196053558812412305 4407788397040169109309229)
          ·
            refine ⟨1652920648890063415990961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4407788397040169109309229 1652920648890063415990961)
            ·
              refine ⟨1239690486667547561993221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652920648890063415990961 1239690486667547561993221)
              ·
                refine ⟨232441966250165167873729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1239690486667547561993221 232441966250165167873729)
                ·
                  refine ⟨174331474687623875905297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232441966250165167873729 174331474687623875905297)
                  ·
                    rfl

theorem cell20_381948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_381948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381948 prefixEnd_381948 := by exact prefixLift 381948
  have htrace : WordTrace (prefixWord ++ tailWord_381948) baseStart_381948 baseEnd_381948 := by
    simpa [prefixWord, tailWord_381948, baseEnd_381948] using wordTrace_append hprefix tailTrace_381948
  have hstable : (prefixWord ++ tailWord_381948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381948).length < 2 ^ (prefixWord ++ tailWord_381948).sum := by decide
  have hdescent : baseEnd_381948 < baseStart_381948 := by decide
  rcases family_descends (prefixWord ++ tailWord_381948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381976 : List Nat := [2, 1, 2, 3, 2, 3, 1, 6]
def baseStart_381976 : Nat := 118140960795 + 381976 * 2 ^ 59
def prefixEnd_381976 : Nat := 4983230072969 + 3 ^ 40 * 381976 * 2
def baseEnd_381976 : Nat := 58114751550193407657283

theorem tailTrace_381976 : CollatzResearch.WordTrace tailWord_381976 prefixEnd_381976 58114751550193407657283 := by
  unfold tailWord_381976
  simp only [CollatzResearch.WordTrace]
  refine ⟨6965904632086831576090891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9287872842782442101454521 6965904632086831576090891)
  ·
    refine ⟨10448856948130247364136337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6965904632086831576090891 10448856948130247364136337)
    ·
      refine ⟨7836642711097685523102253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10448856948130247364136337 7836642711097685523102253)
      ·
        refine ⟨2938741016661632071163345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7836642711097685523102253 2938741016661632071163345)
        ·
          refine ⟨2204055762496224053372509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938741016661632071163345 2204055762496224053372509)
          ·
            refine ⟨826520910936084020014691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2204055762496224053372509 826520910936084020014691)
            ·
              refine ⟨1239781366404126030022037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826520910936084020014691 1239781366404126030022037)
              ·
                refine ⟨58114751550193407657283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1239781366404126030022037 58114751550193407657283)
                ·
                  rfl

theorem cell20_381976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_381976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381976 prefixEnd_381976 := by exact prefixLift 381976
  have htrace : WordTrace (prefixWord ++ tailWord_381976) baseStart_381976 baseEnd_381976 := by
    simpa [prefixWord, tailWord_381976, baseEnd_381976] using wordTrace_append hprefix tailTrace_381976
  have hstable : (prefixWord ++ tailWord_381976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381976).length < 2 ^ (prefixWord ++ tailWord_381976).sum := by decide
  have hdescent : baseEnd_381976 < baseStart_381976 := by decide
  rcases family_descends (prefixWord ++ tailWord_381976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381983 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_381983 : Nat := 118140960795 + 381983 * 2 ^ 59
def prefixEnd_381983 : Nat := 4983230072969 + 3 ^ 40 * 381983 * 2
def baseEnd_381983 : Nat := 174347449641319309738487

theorem tailTrace_381983 : CollatzResearch.WordTrace tailWord_381983 prefixEnd_381983 174347449641319309738487 := by
  unfold tailWord_381983
  simp only [CollatzResearch.WordTrace]
  refine ⟨13932064575148303347686603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9288043050098868898457735 13932064575148303347686603)
  ·
    refine ⟨20898096862722455021529905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13932064575148303347686603 20898096862722455021529905)
    ·
      refine ⟨15673572647041841266147429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20898096862722455021529905 15673572647041841266147429)
      ·
        refine ⟨2938794871320345237402643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15673572647041841266147429 2938794871320345237402643)
        ·
          refine ⟨4408192306980517856103965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2938794871320345237402643 4408192306980517856103965)
          ·
            refine ⟨1653072115117694196038987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4408192306980517856103965 1653072115117694196038987)
            ·
              refine ⟨2479608172676541294058481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653072115117694196038987 2479608172676541294058481)
              ·
                refine ⟨1859706129507405970543861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479608172676541294058481 1859706129507405970543861)
                ·
                  refine ⟨174347449641319309738487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1859706129507405970543861 174347449641319309738487)
                  ·
                    rfl

theorem cell20_381983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_381983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_381983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_381983 prefixEnd_381983 := by exact prefixLift 381983
  have htrace : WordTrace (prefixWord ++ tailWord_381983) baseStart_381983 baseEnd_381983 := by
    simpa [prefixWord, tailWord_381983, baseEnd_381983] using wordTrace_append hprefix tailTrace_381983
  have hstable : (prefixWord ++ tailWord_381983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381983).length < 2 ^ (prefixWord ++ tailWord_381983).sum := by decide
  have hdescent : baseEnd_381983 < baseStart_381983 := by decide
  rcases family_descends (prefixWord ++ tailWord_381983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382017 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 3]
def baseStart_382017 : Nat := 118140960795 + 382017 * 2 ^ 59
def prefixEnd_382017 : Nat := 4983230072969 + 3 ^ 40 * 382017 * 2
def baseEnd_382017 : Nat := 174362968167766302605015

theorem tailTrace_382017 : CollatzResearch.WordTrace tailWord_382017 prefixEnd_382017 174362968167766302605015 := by
  unfold tailWord_382017
  simp only [CollatzResearch.WordTrace]
  refine ⟨13933304657025127154424305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9288869771350084769616203 13933304657025127154424305)
  ·
    refine ⟨10449978492768845365818229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13933304657025127154424305 10449978492768845365818229)
    ·
      refine ⟨979685483697079253045459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10449978492768845365818229 979685483697079253045459)
      ·
        refine ⟨1469528225545618879568189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979685483697079253045459 1469528225545618879568189)
        ·
          refine ⟨551073084579607079838071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1469528225545618879568189 551073084579607079838071)
          ·
            refine ⟨826609626869410619757107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551073084579607079838071 826609626869410619757107)
            ·
              refine ⟨1239914440304115929635661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826609626869410619757107 1239914440304115929635661)
              ·
                refine ⟨464967915114043473613373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1239914440304115929635661 464967915114043473613373)
                ·
                  refine ⟨174362968167766302605015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464967915114043473613373 174362968167766302605015)
                  ·
                    rfl

theorem cell20_382017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_382017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382017 prefixEnd_382017 := by exact prefixLift 382017
  have htrace : WordTrace (prefixWord ++ tailWord_382017) baseStart_382017 baseEnd_382017 := by
    simpa [prefixWord, tailWord_382017, baseEnd_382017] using wordTrace_append hprefix tailTrace_382017
  have hstable : (prefixWord ++ tailWord_382017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382017).length < 2 ^ (prefixWord ++ tailWord_382017).sum := by decide
  have hdescent : baseEnd_382017 < baseStart_382017 := by decide
  rcases family_descends (prefixWord ++ tailWord_382017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382028 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_382028 : Nat := 118140960795 + 382028 * 2 ^ 59
def prefixEnd_382028 : Nat := 4983230072969 + 3 ^ 40 * 382028 * 2
def baseEnd_382028 : Nat := 174367988867499153238303

theorem tailTrace_382028 : CollatzResearch.WordTrace tailWord_382028 prefixEnd_382028 174367988867499153238303 := by
  unfold tailWord_382028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6966852929992638016537369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9289137239990184022049825 6966852929992638016537369)
  ·
    refine ⟨5225139697494478512403027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6966852929992638016537369 5225139697494478512403027)
    ·
      refine ⟨7837709546241717768604541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5225139697494478512403027 7837709546241717768604541)
      ·
        refine ⟨2939141079840644163226703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7837709546241717768604541 2939141079840644163226703)
        ·
          refine ⟨4408711619760966244840055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939141079840644163226703 4408711619760966244840055)
          ·
            refine ⟨6613067429641449367260083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4408711619760966244840055 6613067429641449367260083)
            ·
              refine ⟨9919601144462174050890125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6613067429641449367260083 9919601144462174050890125)
              ·
                refine ⟨3719850429173315269083797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9919601144462174050890125 3719850429173315269083797)
                ·
                  refine ⟨174367988867499153238303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3719850429173315269083797 174367988867499153238303)
                  ·
                    rfl

theorem cell20_382028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_382028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382028 prefixEnd_382028 := by exact prefixLift 382028
  have htrace : WordTrace (prefixWord ++ tailWord_382028) baseStart_382028 baseEnd_382028 := by
    simpa [prefixWord, tailWord_382028, baseEnd_382028] using wordTrace_append hprefix tailTrace_382028
  have hstable : (prefixWord ++ tailWord_382028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382028).length < 2 ^ (prefixWord ++ tailWord_382028).sum := by decide
  have hdescent : baseEnd_382028 < baseStart_382028 := by decide
  rcases family_descends (prefixWord ++ tailWord_382028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382058 : List Nat := [3, 1, 3, 2, 2, 3, 2, 2, 2]
def baseStart_382058 : Nat := 118140960795 + 382058 * 2 ^ 59
def prefixEnd_382058 : Nat := 4983230072969 + 3 ^ 40 * 382058 * 2
def baseEnd_382058 : Nat := 174381681684952382238181

theorem tailTrace_382058 : CollatzResearch.WordTrace tailWord_382058 prefixEnd_382058 174381681684952382238181 := by
  unfold tailWord_382058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3483700012469147789166707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9289866699917727437777885 3483700012469147789166707)
  ·
    refine ⟨5225550018703721683750061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3483700012469147789166707 5225550018703721683750061)
    ·
      refine ⟨1959581257013895631406273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5225550018703721683750061 1959581257013895631406273)
      ·
        refine ⟨1469685942760421723554705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1959581257013895631406273 1469685942760421723554705)
        ·
          refine ⟨1102264457070316292666029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1469685942760421723554705 1102264457070316292666029)
          ·
            refine ⟨413349171401368609749761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1102264457070316292666029 413349171401368609749761)
            ·
              refine ⟨310011878551026457312321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413349171401368609749761 310011878551026457312321)
              ·
                refine ⟨232508908913269842984241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310011878551026457312321 232508908913269842984241)
                ·
                  refine ⟨174381681684952382238181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232508908913269842984241 174381681684952382238181)
                  ·
                    rfl

theorem cell20_382058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_382058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382058 prefixEnd_382058 := by exact prefixLift 382058
  have htrace : WordTrace (prefixWord ++ tailWord_382058) baseStart_382058 baseEnd_382058 := by
    simpa [prefixWord, tailWord_382058, baseEnd_382058] using wordTrace_append hprefix tailTrace_382058
  have hstable : (prefixWord ++ tailWord_382058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382058).length < 2 ^ (prefixWord ++ tailWord_382058).sum := by decide
  have hdescent : baseEnd_382058 < baseStart_382058 := by decide
  rcases family_descends (prefixWord ++ tailWord_382058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382110 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_382110 : Nat := 118140960795 + 382110 * 2 ^ 59
def prefixEnd_382110 : Nat := 4983230072969 + 3 ^ 40 * 382110 * 2
def baseEnd_382110 : Nat := 174405415901871312504635

theorem tailTrace_382110 : CollatzResearch.WordTrace tailWord_382110 prefixEnd_382110 174405415901871312504635 := by
  unfold tailWord_382110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1742087080711025504694973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9291131097125469358373189 1742087080711025504694973)
  ·
    refine ⟨653282655266634564260615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1742087080711025504694973 653282655266634564260615)
    ·
      refine ⟨979923982899951846390923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 653282655266634564260615 979923982899951846390923)
      ·
        refine ⟨1469885974349927769586385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979923982899951846390923 1469885974349927769586385)
        ·
          refine ⟨1102414480762445827189789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1469885974349927769586385 1102414480762445827189789)
          ·
            refine ⟨413405430285917185196171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1102414480762445827189789 413405430285917185196171)
            ·
              refine ⟨620108145428875777794257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413405430285917185196171 620108145428875777794257)
              ·
                refine ⟨465081109071656833345693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620108145428875777794257 465081109071656833345693)
                ·
                  refine ⟨174405415901871312504635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465081109071656833345693 174405415901871312504635)
                  ·
                    rfl

theorem cell20_382110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_382110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382110 prefixEnd_382110 := by exact prefixLift 382110
  have htrace : WordTrace (prefixWord ++ tailWord_382110) baseStart_382110 baseEnd_382110 := by
    simpa [prefixWord, tailWord_382110, baseEnd_382110] using wordTrace_append hprefix tailTrace_382110
  have hstable : (prefixWord ++ tailWord_382110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382110).length < 2 ^ (prefixWord ++ tailWord_382110).sum := by decide
  have hdescent : baseEnd_382110 < baseStart_382110 := by decide
  rcases family_descends (prefixWord ++ tailWord_382110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382145 : List Nat := [1, 2, 6, 1, 1, 2, 1, 6]
def baseStart_382145 : Nat := 118140960795 + 382145 * 2 ^ 59
def prefixEnd_382145 : Nat := 4983230072969 + 3 ^ 40 * 382145 * 2
def baseEnd_382145 : Nat := 58140463618522248779275

theorem tailTrace_382145 : CollatzResearch.WordTrace tailWord_382145 prefixEnd_382145 58140463618522248779275 := by
  unfold tailWord_382145
  simp only [CollatzResearch.WordTrace]
  refine ⟨13937973200561405015083889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9291982133707603343389259 13937973200561405015083889)
  ·
    refine ⟨10453479900421053761312917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13937973200561405015083889 10453479900421053761312917)
    ·
      refine ⟨490006870332236895061543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10453479900421053761312917 490006870332236895061543)
      ·
        refine ⟨735010305498355342592315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490006870332236895061543 735010305498355342592315)
        ·
          refine ⟨1102515458247533013888473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735010305498355342592315 1102515458247533013888473)
          ·
            refine ⟨826886593685649760416355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102515458247533013888473 826886593685649760416355)
            ·
              refine ⟨1240329890528474640624533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826886593685649760416355 1240329890528474640624533)
              ·
                refine ⟨58140463618522248779275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1240329890528474640624533 58140463618522248779275)
                ·
                  rfl

theorem cell20_382145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 6].length) (baseStart_382145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382145 prefixEnd_382145 := by exact prefixLift 382145
  have htrace : WordTrace (prefixWord ++ tailWord_382145) baseStart_382145 baseEnd_382145 := by
    simpa [prefixWord, tailWord_382145, baseEnd_382145] using wordTrace_append hprefix tailTrace_382145
  have hstable : (prefixWord ++ tailWord_382145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382145).length < 2 ^ (prefixWord ++ tailWord_382145).sum := by decide
  have hdescent : baseEnd_382145 < baseStart_382145 := by decide
  rcases family_descends (prefixWord ++ tailWord_382145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382159 : List Nat := [1, 1, 2, 1, 1, 3, 2, 7, 2]
def baseStart_382159 : Nat := 118140960795 + 382159 * 2 ^ 59
def prefixEnd_382159 : Nat := 4983230072969 + 3 ^ 40 * 382159 * 2
def baseEnd_382159 : Nat := 174427780837044919871101

theorem tailTrace_382159 : CollatzResearch.WordTrace tailWord_382159 prefixEnd_382159 174427780837044919871101 := by
  unfold tailWord_382159
  simp only [CollatzResearch.WordTrace]
  refine ⟨13938483822510685406093531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9292322548340456937395687 13938483822510685406093531)
  ·
    refine ⟨20907725733766028109140297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13938483822510685406093531 20907725733766028109140297)
    ·
      refine ⟨15680794300324521081855223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20907725733766028109140297 15680794300324521081855223)
      ·
        refine ⟨23521191450486781622782835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15680794300324521081855223 23521191450486781622782835)
        ·
          refine ⟨35281787175730172434174253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23521191450486781622782835 35281787175730172434174253)
          ·
            refine ⟨13230670190898814662815345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35281787175730172434174253 13230670190898814662815345)
            ·
              refine ⟨9923002643174110997111509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13230670190898814662815345 9923002643174110997111509)
              ·
                refine ⟨232570374449393226494801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9923002643174110997111509 232570374449393226494801)
                ·
                  refine ⟨174427780837044919871101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232570374449393226494801 174427780837044919871101)
                  ·
                    rfl

theorem cell20_382159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 2].length) (baseStart_382159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382159 prefixEnd_382159 := by exact prefixLift 382159
  have htrace : WordTrace (prefixWord ++ tailWord_382159) baseStart_382159 baseEnd_382159 := by
    simpa [prefixWord, tailWord_382159, baseEnd_382159] using wordTrace_append hprefix tailTrace_382159
  have hstable : (prefixWord ++ tailWord_382159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382159).length < 2 ^ (prefixWord ++ tailWord_382159).sum := by decide
  have hdescent : baseEnd_382159 < baseStart_382159 := by decide
  rcases family_descends (prefixWord ++ tailWord_382159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382183 : List Nat := [1, 1, 5, 3, 2, 1, 2, 5]
def baseStart_382183 : Nat := 118140960795 + 382183 * 2 ^ 59
def prefixEnd_382183 : Nat := 4983230072969 + 3 ^ 40 * 382183 * 2
def baseEnd_382183 : Nat := 58146245030335834357001

theorem tailTrace_382183 : CollatzResearch.WordTrace tailWord_382183 prefixEnd_382183 58146245030335834357001 := by
  unfold tailWord_382183
  simp only [CollatzResearch.WordTrace]
  refine ⟨13939359174423737504967203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9292906116282491669978135 13939359174423737504967203)
  ·
    refine ⟨20909038761635606257450805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13939359174423737504967203 20909038761635606257450805)
    ·
      refine ⟨1960222383903338086636013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20909038761635606257450805 1960222383903338086636013)
      ·
        refine ⟨735083393963751782488505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1960222383903338086636013 735083393963751782488505)
        ·
          refine ⟨551312545472813836866379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735083393963751782488505 551312545472813836866379)
          ·
            refine ⟨826968818209220755299569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551312545472813836866379 826968818209220755299569)
            ·
              refine ⟨620226613656915566474677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826968818209220755299569 620226613656915566474677)
              ·
                refine ⟨58146245030335834357001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 620226613656915566474677 58146245030335834357001)
                ·
                  rfl

theorem cell20_382183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 5].length) (baseStart_382183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382183 prefixEnd_382183 := by exact prefixLift 382183
  have htrace : WordTrace (prefixWord ++ tailWord_382183) baseStart_382183 baseEnd_382183 := by
    simpa [prefixWord, tailWord_382183, baseEnd_382183] using wordTrace_append hprefix tailTrace_382183
  have hstable : (prefixWord ++ tailWord_382183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382183).length < 2 ^ (prefixWord ++ tailWord_382183).sum := by decide
  have hdescent : baseEnd_382183 < baseStart_382183 := by decide
  rcases family_descends (prefixWord ++ tailWord_382183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382187 : List Nat := [1, 1, 1, 1, 2, 6, 1, 7]
def baseStart_382187 : Nat := 118140960795 + 382187 * 2 ^ 59
def prefixEnd_382187 : Nat := 4983230072969 + 3 ^ 40 * 382187 * 2
def baseEnd_382187 : Nat := 58146853600000422312551

theorem tailTrace_382187 : CollatzResearch.WordTrace tailWord_382187 prefixEnd_382187 58146853600000422312551 := by
  unfold tailWord_382187
  simp only [CollatzResearch.WordTrace]
  refine ⟨13939505066409246188112815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9293003377606164125408543 13939505066409246188112815)
  ·
    refine ⟨20909257599613869282169223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13939505066409246188112815 20909257599613869282169223)
    ·
      refine ⟨31363886399420803923253835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20909257599613869282169223 31363886399420803923253835)
      ·
        refine ⟨47045829599131205884880753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31363886399420803923253835 47045829599131205884880753)
        ·
          refine ⟨35284372199348404413660565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47045829599131205884880753 35284372199348404413660565)
          ·
            refine ⟨1653954946844456456890339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35284372199348404413660565 1653954946844456456890339)
            ·
              refine ⟨2480932420266684685335509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653954946844456456890339 2480932420266684685335509)
              ·
                refine ⟨58146853600000422312551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2480932420266684685335509 58146853600000422312551)
                ·
                  rfl

theorem cell20_382187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_382187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382187 prefixEnd_382187 := by exact prefixLift 382187
  have htrace : WordTrace (prefixWord ++ tailWord_382187) baseStart_382187 baseEnd_382187 := by
    simpa [prefixWord, tailWord_382187, baseEnd_382187] using wordTrace_append hprefix tailTrace_382187
  have hstable : (prefixWord ++ tailWord_382187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382187).length < 2 ^ (prefixWord ++ tailWord_382187).sum := by decide
  have hdescent : baseEnd_382187 < baseStart_382187 := by decide
  rcases family_descends (prefixWord ++ tailWord_382187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382256 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_382256 : Nat := 118140960795 + 382256 * 2 ^ 59
def prefixEnd_382256 : Nat := 4983230072969 + 3 ^ 40 * 382256 * 2
def baseEnd_382256 : Nat := 174472054280143693637371

theorem tailTrace_382256 : CollatzResearch.WordTrace tailWord_382256 prefixEnd_382256 174472054280143693637371 := by
  unfold tailWord_382256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6971010851579635486187311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9294681135439513981583081 6971010851579635486187311)
  ·
    refine ⟨10456516277369453229280967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6971010851579635486187311 10456516277369453229280967)
    ·
      refine ⟨15684774416054179843921451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10456516277369453229280967 15684774416054179843921451)
      ·
        refine ⟨23527161624081269765882177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15684774416054179843921451 23527161624081269765882177)
        ·
          refine ⟨17645371218060952324411633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23527161624081269765882177 17645371218060952324411633)
          ·
            refine ⟨13234028413545714243308725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17645371218060952324411633 13234028413545714243308725)
            ·
              refine ⟨1240690163769910710310193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13234028413545714243308725 1240690163769910710310193)
              ·
                refine ⟨930517622827433032732645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1240690163769910710310193 930517622827433032732645)
                ·
                  refine ⟨174472054280143693637371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 930517622827433032732645 174472054280143693637371)
                  ·
                    rfl

theorem cell20_382256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_382256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382256 prefixEnd_382256 := by exact prefixLift 382256
  have htrace : WordTrace (prefixWord ++ tailWord_382256) baseStart_382256 baseEnd_382256 := by
    simpa [prefixWord, tailWord_382256, baseEnd_382256] using wordTrace_append hprefix tailTrace_382256
  have hstable : (prefixWord ++ tailWord_382256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382256).length < 2 ^ (prefixWord ++ tailWord_382256).sum := by decide
  have hdescent : baseEnd_382256 < baseStart_382256 := by decide
  rcases family_descends (prefixWord ++ tailWord_382256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382314 : List Nat := [3, 1, 3, 3, 2, 2, 2, 4]
def baseStart_382314 : Nat := 118140960795 + 382314 * 2 ^ 59
def prefixEnd_382314 : Nat := 4983230072969 + 3 ^ 40 * 382314 * 2
def baseEnd_382314 : Nat := 58166175686851089901267

theorem tailTrace_382314 : CollatzResearch.WordTrace tailWord_382314 prefixEnd_382314 58166175686851089901267 := by
  unfold tailWord_382314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486034284237286719496499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9296091424632764585323997 3486034284237286719496499)
  ·
    refine ⟨5229051426355930079244749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3486034284237286719496499 5229051426355930079244749)
    ·
      refine ⟨1960894284883473779716781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5229051426355930079244749 1960894284883473779716781)
      ·
        refine ⟨735335356831302667393793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1960894284883473779716781 735335356831302667393793)
        ·
          refine ⟨551501517623477000545345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735335356831302667393793 551501517623477000545345)
          ·
            refine ⟨413626138217607750409009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551501517623477000545345 413626138217607750409009)
            ·
              refine ⟨310219603663205812806757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413626138217607750409009 310219603663205812806757)
              ·
                refine ⟨58166175686851089901267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310219603663205812806757 58166175686851089901267)
                ·
                  rfl

theorem cell20_382314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_382314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382314 prefixEnd_382314 := by exact prefixLift 382314
  have htrace : WordTrace (prefixWord ++ tailWord_382314) baseStart_382314 baseEnd_382314 := by
    simpa [prefixWord, tailWord_382314, baseEnd_382314] using wordTrace_append hprefix tailTrace_382314
  have hstable : (prefixWord ++ tailWord_382314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382314).length < 2 ^ (prefixWord ++ tailWord_382314).sum := by decide
  have hdescent : baseEnd_382314 < baseStart_382314 := by decide
  rcases family_descends (prefixWord ++ tailWord_382314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382339 : List Nat := [1, 1, 1, 3, 5, 1, 8]
def baseStart_382339 : Nat := 118140960795 + 382339 * 2 ^ 59
def prefixEnd_382339 : Nat := 4983230072969 + 3 ^ 40 * 382339 * 2
def baseEnd_382339 : Nat := 19389993082418254874485

theorem tailTrace_382339 : CollatzResearch.WordTrace tailWord_382339 prefixEnd_382339 19389993082418254874485 := by
  unfold tailWord_382339
  simp only [CollatzResearch.WordTrace]
  refine ⟨13945048961858576147646071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9296699307905717431764047 13945048961858576147646071)
  ·
    refine ⟨20917573442787864221469107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13945048961858576147646071 20917573442787864221469107)
    ·
      refine ⟨31376360164181796332203661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20917573442787864221469107 31376360164181796332203661)
      ·
        refine ⟨11766135061568173624576373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31376360164181796332203661 11766135061568173624576373)
        ·
          refine ⟨1103075162022016277304035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11766135061568173624576373 1103075162022016277304035)
          ·
            refine ⟨1654612743033024415956053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103075162022016277304035 1654612743033024415956053)
            ·
              refine ⟨19389993082418254874485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1654612743033024415956053 19389993082418254874485)
              ·
                rfl

theorem cell20_382339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 8].length) (baseStart_382339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382339 prefixEnd_382339 := by exact prefixLift 382339
  have htrace : WordTrace (prefixWord ++ tailWord_382339) baseStart_382339 baseEnd_382339 := by
    simpa [prefixWord, tailWord_382339, baseEnd_382339] using wordTrace_append hprefix tailTrace_382339
  have hstable : (prefixWord ++ tailWord_382339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382339).length < 2 ^ (prefixWord ++ tailWord_382339).sum := by decide
  have hdescent : baseEnd_382339 < baseStart_382339 := by decide
  rcases family_descends (prefixWord ++ tailWord_382339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382345 : List Nat := [1, 2, 1, 1, 7, 1, 3, 2, 2]
def baseStart_382345 : Nat := 118140960795 + 382345 * 2 ^ 59
def prefixEnd_382345 : Nat := 4983230072969 + 3 ^ 40 * 382345 * 2
def baseEnd_382345 : Nat := 174512676305254939670341

theorem tailTrace_382345 : CollatzResearch.WordTrace tailWord_382345 prefixEnd_382345 174512676305254939670341 := by
  unfold tailWord_382345
  simp only [CollatzResearch.WordTrace]
  refine ⟨13945267799836839172364489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9296845199891226114909659 13945267799836839172364489)
  ·
    refine ⟨10458950849877629379273367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13945267799836839172364489 10458950849877629379273367)
    ·
      refine ⟨15688426274816444068910051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10458950849877629379273367 15688426274816444068910051)
      ·
        refine ⟨23532639412224666103365077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15688426274816444068910051 23532639412224666103365077)
        ·
          refine ⟨551546236224015611797619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 23532639412224666103365077 551546236224015611797619)
          ·
            refine ⟨827319354336023417696429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551546236224015611797619 827319354336023417696429)
            ·
              refine ⟨310244757876008781636161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 827319354336023417696429 310244757876008781636161)
              ·
                refine ⟨232683568407006586227121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310244757876008781636161 232683568407006586227121)
                ·
                  refine ⟨174512676305254939670341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232683568407006586227121 174512676305254939670341)
                  ·
                    rfl

theorem cell20_382345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_382345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382345 prefixEnd_382345 := by exact prefixLift 382345
  have htrace : WordTrace (prefixWord ++ tailWord_382345) baseStart_382345 baseEnd_382345 := by
    simpa [prefixWord, tailWord_382345, baseEnd_382345] using wordTrace_append hprefix tailTrace_382345
  have hstable : (prefixWord ++ tailWord_382345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382345).length < 2 ^ (prefixWord ++ tailWord_382345).sum := by decide
  have hdescent : baseEnd_382345 < baseStart_382345 := by decide
  rcases family_descends (prefixWord ++ tailWord_382345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382356 : List Nat := [2, 4, 2, 1, 2, 1, 1, 7]
def baseStart_382356 : Nat := 118140960795 + 382356 * 2 ^ 59
def prefixEnd_382356 : Nat := 4983230072969 + 3 ^ 40 * 382356 * 2
def baseEnd_382356 : Nat := 58172565668329263434543

theorem tailTrace_382356 : CollatzResearch.WordTrace tailWord_382356 prefixEnd_382356 58172565668329263434543 := by
  unfold tailWord_382356
  simp only [CollatzResearch.WordTrace]
  refine ⟨6972834501398494025507461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9297112668531325367343281 6972834501398494025507461)
  ·
    refine ⟨1307406469012217629782649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6972834501398494025507461 1307406469012217629782649)
    ·
      refine ⟨980554851759163222336987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1307406469012217629782649 980554851759163222336987)
      ·
        refine ⟨1470832277638744833505481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 980554851759163222336987 1470832277638744833505481)
        ·
          refine ⟨1103124208229058625129111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1470832277638744833505481 1103124208229058625129111)
          ·
            refine ⟨1654686312343587937693667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103124208229058625129111 1654686312343587937693667)
            ·
              refine ⟨2482029468515381906540501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654686312343587937693667 2482029468515381906540501)
              ·
                refine ⟨58172565668329263434543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2482029468515381906540501 58172565668329263434543)
                ·
                  rfl

theorem cell20_382356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_382356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382356 prefixEnd_382356 := by exact prefixLift 382356
  have htrace : WordTrace (prefixWord ++ tailWord_382356) baseStart_382356 baseEnd_382356 := by
    simpa [prefixWord, tailWord_382356, baseEnd_382356] using wordTrace_append hprefix tailTrace_382356
  have hstable : (prefixWord ++ tailWord_382356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382356).length < 2 ^ (prefixWord ++ tailWord_382356).sum := by decide
  have hdescent : baseEnd_382356 < baseStart_382356 := by decide
  rcases family_descends (prefixWord ++ tailWord_382356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382384 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_382384 : Nat := 118140960795 + 382384 * 2 ^ 59
def prefixEnd_382384 : Nat := 4983230072969 + 3 ^ 40 * 382384 * 2
def baseEnd_382384 : Nat := 174530476967944137370181

theorem tailTrace_382384 : CollatzResearch.WordTrace tailWord_382384 prefixEnd_382384 174530476967944137370181 := by
  unfold tailWord_382384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6973345123347774416517103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9297793497797032555356137 6973345123347774416517103)
  ·
    refine ⟨10460017685021661624775655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6973345123347774416517103 10460017685021661624775655)
    ·
      refine ⟨15690026527532492437163483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10460017685021661624775655 15690026527532492437163483)
      ·
        refine ⟨23535039791298738655745225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15690026527532492437163483 23535039791298738655745225)
        ·
          refine ⟨17651279843474053991808919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23535039791298738655745225 17651279843474053991808919)
          ·
            refine ⟨26476919765211080987713379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17651279843474053991808919 26476919765211080987713379)
            ·
              refine ⟨39715379647816621481570069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26476919765211080987713379 39715379647816621481570069)
              ·
                refine ⟨1861658420991404131948597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39715379647816621481570069 1861658420991404131948597)
                ·
                  refine ⟨174530476967944137370181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1861658420991404131948597 174530476967944137370181)
                  ·
                    rfl

theorem cell20_382384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_382384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382384 prefixEnd_382384 := by exact prefixLift 382384
  have htrace : WordTrace (prefixWord ++ tailWord_382384) baseStart_382384 baseEnd_382384 := by
    simpa [prefixWord, tailWord_382384, baseEnd_382384] using wordTrace_append hprefix tailTrace_382384
  have hstable : (prefixWord ++ tailWord_382384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382384).length < 2 ^ (prefixWord ++ tailWord_382384).sum := by decide
  have hdescent : baseEnd_382384 < baseStart_382384 := by decide
  rcases family_descends (prefixWord ++ tailWord_382384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382408 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_382408 : Nat := 118140960795 + 382408 * 2 ^ 59
def prefixEnd_382408 : Nat := 4983230072969 + 3 ^ 40 * 382408 * 2
def baseEnd_382408 : Nat := 174541431221906720570083

theorem tailTrace_382408 : CollatzResearch.WordTrace tailWord_382408 prefixEnd_382408 174541431221906720570083 := by
  unfold tailWord_382408
  simp only [CollatzResearch.WordTrace]
  refine ⟨6973782799304300465953939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9298377065739067287938585 6973782799304300465953939)
  ·
    refine ⟨10460674198956450698930909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6973782799304300465953939 10460674198956450698930909)
    ·
      refine ⟨3922752824608669012099091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10460674198956450698930909 3922752824608669012099091)
      ·
        refine ⟨5884129236913003518148637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922752824608669012099091 5884129236913003518148637)
        ·
          refine ⟨2206548463842376319305739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5884129236913003518148637 2206548463842376319305739)
          ·
            refine ⟨3309822695763564478958609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206548463842376319305739 3309822695763564478958609)
            ·
              refine ⟨2482367021822673359218957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3309822695763564478958609 2482367021822673359218957)
              ·
                refine ⟨930887633183502509707109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2482367021822673359218957 930887633183502509707109)
                ·
                  refine ⟨174541431221906720570083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 930887633183502509707109 174541431221906720570083)
                  ·
                    rfl

theorem cell20_382408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_382408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382408 prefixEnd_382408 := by exact prefixLift 382408
  have htrace : WordTrace (prefixWord ++ tailWord_382408) baseStart_382408 baseEnd_382408 := by
    simpa [prefixWord, tailWord_382408, baseEnd_382408] using wordTrace_append hprefix tailTrace_382408
  have hstable : (prefixWord ++ tailWord_382408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382408).length < 2 ^ (prefixWord ++ tailWord_382408).sum := by decide
  have hdescent : baseEnd_382408 < baseStart_382408 := by decide
  rcases family_descends (prefixWord ++ tailWord_382408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382415 : List Nat := [1, 1, 2, 1, 1, 4, 5, 5]
def baseStart_382415 : Nat := 118140960795 + 382415 * 2 ^ 59
def prefixEnd_382415 : Nat := 4983230072969 + 3 ^ 40 * 382415 * 2
def baseEnd_382415 : Nat := 58181542070881935778907

theorem tailTrace_382415 : CollatzResearch.WordTrace tailWord_382415 prefixEnd_382415 58181542070881935778907 := by
  unfold tailWord_382415
  simp only [CollatzResearch.WordTrace]
  refine ⟨13947820909583241127412699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9298547273055494084941799 13947820909583241127412699)
  ·
    refine ⟨20921731364374861691119049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13947820909583241127412699 20921731364374861691119049)
    ·
      refine ⟨15691298523281146268339287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20921731364374861691119049 15691298523281146268339287)
      ·
        refine ⟨23536947784921719402508931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15691298523281146268339287 23536947784921719402508931)
        ·
          refine ⟨35305421677382579103763397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23536947784921719402508931 35305421677382579103763397)
          ·
            refine ⟨6619766564509233581955637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35305421677382579103763397 6619766564509233581955637)
            ·
              refine ⟨620603115422740648308341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6619766564509233581955637 620603115422740648308341)
              ·
                refine ⟨58181542070881935778907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 620603115422740648308341 58181542070881935778907)
                ·
                  rfl

theorem cell20_382415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_382415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382415 prefixEnd_382415 := by exact prefixLift 382415
  have htrace : WordTrace (prefixWord ++ tailWord_382415) baseStart_382415 baseEnd_382415 := by
    simpa [prefixWord, tailWord_382415, baseEnd_382415] using wordTrace_append hprefix tailTrace_382415
  have hstable : (prefixWord ++ tailWord_382415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382415).length < 2 ^ (prefixWord ++ tailWord_382415).sum := by decide
  have hdescent : baseEnd_382415 < baseStart_382415 := by decide
  rcases family_descends (prefixWord ++ tailWord_382415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382446 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_382446 : Nat := 118140960795 + 382446 * 2 ^ 59
def prefixEnd_382446 : Nat := 4983230072969 + 3 ^ 40 * 382446 * 2
def baseEnd_382446 : Nat := 174558775457347477303261

theorem tailTrace_382446 : CollatzResearch.WordTrace tailWord_382446 prefixEnd_382446 174558775457347477303261 := by
  unfold tailWord_382446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743618946558866677723899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9299301048313955614527461 1743618946558866677723899)
  ·
    refine ⟨2615428419838300016585849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1743618946558866677723899 2615428419838300016585849)
    ·
      refine ⟨1961571314878725012439387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2615428419838300016585849 1961571314878725012439387)
      ·
        refine ⟨2942356972318087518659081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1961571314878725012439387 2942356972318087518659081)
        ·
          refine ⟨2206767729238565638994311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2942356972318087518659081 2206767729238565638994311)
          ·
            refine ⟨3310151593857848458491467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206767729238565638994311 3310151593857848458491467)
            ·
              refine ⟨4965227390786772687737201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310151593857848458491467 4965227390786772687737201)
              ·
                refine ⟨3723920543090079515802901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4965227390786772687737201 3723920543090079515802901)
                ·
                  refine ⟨174558775457347477303261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3723920543090079515802901 174558775457347477303261)
                  ·
                    rfl

theorem cell20_382446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_382446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382446 prefixEnd_382446 := by exact prefixLift 382446
  have htrace : WordTrace (prefixWord ++ tailWord_382446) baseStart_382446 baseEnd_382446 := by
    simpa [prefixWord, tailWord_382446, baseEnd_382446] using wordTrace_append hprefix tailTrace_382446
  have hstable : (prefixWord ++ tailWord_382446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382446).length < 2 ^ (prefixWord ++ tailWord_382446).sum := by decide
  have hdescent : baseEnd_382446 < baseStart_382446 := by decide
  rcases family_descends (prefixWord ++ tailWord_382446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382456 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 3]
def baseStart_382456 : Nat := 118140960795 + 382456 * 2 ^ 59
def prefixEnd_382456 : Nat := 4983230072969 + 3 ^ 40 * 382456 * 2
def baseEnd_382456 : Nat := 174563339729831886969887

theorem tailTrace_382456 : CollatzResearch.WordTrace tailWord_382456 prefixEnd_382456 174563339729831886969887 := by
  unfold tailWord_382456
  simp only [CollatzResearch.WordTrace]
  refine ⟨6974658151217352564827611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9299544201623136753103481 6974658151217352564827611)
  ·
    refine ⟨10461987226826028847241417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6974658151217352564827611 10461987226826028847241417)
    ·
      refine ⟨7846490420119521635431063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10461987226826028847241417 7846490420119521635431063)
      ·
        refine ⟨11769735630179282453146595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7846490420119521635431063 11769735630179282453146595)
        ·
          refine ⟨17654603445268923679719893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11769735630179282453146595 17654603445268923679719893)
          ·
            refine ⟨413779768248490398743435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17654603445268923679719893 413779768248490398743435)
            ·
              refine ⟨620669652372735598115153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413779768248490398743435 620669652372735598115153)
              ·
                refine ⟨465502239279551698586365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620669652372735598115153 465502239279551698586365)
                ·
                  refine ⟨174563339729831886969887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465502239279551698586365 174563339729831886969887)
                  ·
                    rfl

theorem cell20_382456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_382456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382456 prefixEnd_382456 := by exact prefixLift 382456
  have htrace : WordTrace (prefixWord ++ tailWord_382456) baseStart_382456 baseEnd_382456 := by
    simpa [prefixWord, tailWord_382456, baseEnd_382456] using wordTrace_append hprefix tailTrace_382456
  have hstable : (prefixWord ++ tailWord_382456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382456).length < 2 ^ (prefixWord ++ tailWord_382456).sum := by decide
  have hdescent : baseEnd_382456 < baseStart_382456 := by decide
  rcases family_descends (prefixWord ++ tailWord_382456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382543 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_382543 : Nat := 118140960795 + 382543 * 2 ^ 59
def prefixEnd_382543 : Nat := 4983230072969 + 3 ^ 40 * 382543 * 2
def baseEnd_382543 : Nat := 174603048900446251069531

theorem tailTrace_382543 : CollatzResearch.WordTrace tailWord_382543 prefixEnd_382543 174603048900446251069531 := by
  unfold tailWord_382543
  simp only [CollatzResearch.WordTrace]
  refine ⟨13952489453119518988072283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9301659635413012658714855 13952489453119518988072283)
  ·
    refine ⟨20928734179679278482108425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13952489453119518988072283 20928734179679278482108425)
    ·
      refine ⟨15696550634759458861581319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20928734179679278482108425 15696550634759458861581319)
      ·
        refine ⟨23544825952139188292371979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15696550634759458861581319 23544825952139188292371979)
        ·
          refine ⟨35317238928208782438557969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23544825952139188292371979 35317238928208782438557969)
          ·
            refine ⟨26487929196156586828918477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35317238928208782438557969 26487929196156586828918477)
            ·
              refine ⟨9932973448558720060844429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26487929196156586828918477 9932973448558720060844429)
              ·
                refine ⟨3724865043209520022816661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9932973448558720060844429 3724865043209520022816661)
                ·
                  refine ⟨174603048900446251069531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3724865043209520022816661 174603048900446251069531)
                  ·
                    rfl

theorem cell20_382543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_382543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382543 prefixEnd_382543 := by exact prefixLift 382543
  have htrace : WordTrace (prefixWord ++ tailWord_382543) baseStart_382543 baseEnd_382543 := by
    simpa [prefixWord, tailWord_382543, baseEnd_382543] using wordTrace_append hprefix tailTrace_382543
  have hstable : (prefixWord ++ tailWord_382543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382543).length < 2 ^ (prefixWord ++ tailWord_382543).sum := by decide
  have hdescent : baseEnd_382543 < baseStart_382543 := by decide
  rcases family_descends (prefixWord ++ tailWord_382543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382570 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_382570 : Nat := 118140960795 + 382570 * 2 ^ 59
def prefixEnd_382570 : Nat := 4983230072969 + 3 ^ 40 * 382570 * 2
def baseEnd_382570 : Nat := 174615372436154157169421

theorem tailTrace_382570 : CollatzResearch.WordTrace tailWord_382570 prefixEnd_382570 174615372436154157169421 := by
  unfold tailWord_382570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3488368556005425649826291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9302316149347801732870109 3488368556005425649826291)
  ·
    refine ⟨5232552834008138474739437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3488368556005425649826291 5232552834008138474739437)
    ·
      refine ⟨1962207312753051928027289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5232552834008138474739437 1962207312753051928027289)
      ·
        refine ⟨1471655484564788946020467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1962207312753051928027289 1471655484564788946020467)
        ·
          refine ⟨2207483226847183419030701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471655484564788946020467 2207483226847183419030701)
          ·
            refine ⟨827806210067693782136513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2207483226847183419030701 827806210067693782136513)
            ·
              refine ⟨620854657550770336602385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827806210067693782136513 620854657550770336602385)
              ·
                refine ⟨465640993163077752451789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620854657550770336602385 465640993163077752451789)
                ·
                  refine ⟨174615372436154157169421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465640993163077752451789 174615372436154157169421)
                  ·
                    rfl

theorem cell20_382570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_382570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382570 prefixEnd_382570 := by exact prefixLift 382570
  have htrace : WordTrace (prefixWord ++ tailWord_382570) baseStart_382570 baseEnd_382570 := by
    simpa [prefixWord, tailWord_382570, baseEnd_382570] using wordTrace_append hprefix tailTrace_382570
  have hstable : (prefixWord ++ tailWord_382570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382570).length < 2 ^ (prefixWord ++ tailWord_382570).sum := by decide
  have hdescent : baseEnd_382570 < baseStart_382570 := by decide
  rcases family_descends (prefixWord ++ tailWord_382570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382615 : List Nat := [1, 1, 3, 3, 2, 2, 1, 5, 2]
def baseStart_382615 : Nat := 118140960795 + 382615 * 2 ^ 59
def prefixEnd_382615 : Nat := 4983230072969 + 3 ^ 40 * 382615 * 2
def baseEnd_382615 : Nat := 174635911662334000669237

theorem tailTrace_382615 : CollatzResearch.WordTrace tailWord_382615 prefixEnd_382615 174635911662334000669237 := by
  unfold tailWord_382615
  simp only [CollatzResearch.WordTrace]
  refine ⟨13955115508858675284693299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9303410339239116856462199 13955115508858675284693299)
  ·
    refine ⟨20932673263288012927039949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13955115508858675284693299 20932673263288012927039949)
    ·
      refine ⟨7849752473733004847639981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20932673263288012927039949 7849752473733004847639981)
      ·
        refine ⟨2943657177649876817864993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7849752473733004847639981 2943657177649876817864993)
        ·
          refine ⟨2207742883237407613398745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2943657177649876817864993 2207742883237407613398745)
          ·
            refine ⟨1655807162428055710049059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2207742883237407613398745 1655807162428055710049059)
            ·
              refine ⟨2483710743642083565073589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655807162428055710049059 2483710743642083565073589)
              ·
                refine ⟨232847882216445334225649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2483710743642083565073589 232847882216445334225649)
                ·
                  refine ⟨174635911662334000669237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232847882216445334225649 174635911662334000669237)
                  ·
                    rfl

theorem cell20_382615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 2].length) (baseStart_382615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382615 prefixEnd_382615 := by exact prefixLift 382615
  have htrace : WordTrace (prefixWord ++ tailWord_382615) baseStart_382615 baseEnd_382615 := by
    simpa [prefixWord, tailWord_382615, baseEnd_382615] using wordTrace_append hprefix tailTrace_382615
  have hstable : (prefixWord ++ tailWord_382615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382615).length < 2 ^ (prefixWord ++ tailWord_382615).sum := by decide
  have hdescent : baseEnd_382615 < baseStart_382615 := by decide
  rcases family_descends (prefixWord ++ tailWord_382615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382622 : List Nat := [4, 3, 1, 1, 1, 3, 7]
def baseStart_382622 : Nat := 118140960795 + 382622 * 2 ^ 59
def prefixEnd_382622 : Nat := 4983230072969 + 3 ^ 40 * 382622 * 2
def baseEnd_382622 : Nat := 19404345183674787492875

theorem tailTrace_382622 : CollatzResearch.WordTrace tailWord_382622 prefixEnd_382622 19404345183674787492875 := by
  unfold tailWord_382622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744421352479164435024765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9303580546555543653465413 1744421352479164435024765)
  ·
    refine ⟨654158007179686663134287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1744421352479164435024765 654158007179686663134287)
    ·
      refine ⟨981237010769529994701431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 654158007179686663134287 981237010769529994701431)
      ·
        refine ⟨1471855516154294992052147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 981237010769529994701431 1471855516154294992052147)
        ·
          refine ⟨2207783274231442488078221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471855516154294992052147 2207783274231442488078221)
          ·
            refine ⟨827918727836790933029333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2207783274231442488078221 827918727836790933029333)
            ·
              refine ⟨19404345183674787492875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 827918727836790933029333 19404345183674787492875)
              ·
                rfl

theorem cell20_382622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 7].length) (baseStart_382622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382622 prefixEnd_382622 := by exact prefixLift 382622
  have htrace : WordTrace (prefixWord ++ tailWord_382622) baseStart_382622 baseEnd_382622 := by
    simpa [prefixWord, tailWord_382622, baseEnd_382622] using wordTrace_append hprefix tailTrace_382622
  have hstable : (prefixWord ++ tailWord_382622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382622).length < 2 ^ (prefixWord ++ tailWord_382622).sum := by decide
  have hdescent : baseEnd_382622 < baseStart_382622 := by decide
  rcases family_descends (prefixWord ++ tailWord_382622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382629 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 3]
def baseStart_382629 : Nat := 118140960795 + 382629 * 2 ^ 59
def prefixEnd_382629 : Nat := 4983230072969 + 3 ^ 40 * 382629 * 2
def baseEnd_382629 : Nat := 174642301643812174202513

theorem tailTrace_382629 : CollatzResearch.WordTrace tailWord_382629 prefixEnd_382629 174642301643812174202513 := by
  unfold tailWord_382629
  simp only [CollatzResearch.WordTrace]
  refine ⟨13955626130807955675702941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9303750753871970450468627 13955626130807955675702941)
  ·
    refine ⟨5233359799052983378388603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13955626130807955675702941 5233359799052983378388603)
    ·
      refine ⟨7850039698579475067582905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5233359799052983378388603 7850039698579475067582905)
      ·
        refine ⟨5887529773934606300687179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7850039698579475067582905 5887529773934606300687179)
        ·
          refine ⟨8831294660901909451030769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5887529773934606300687179 8831294660901909451030769)
          ·
            refine ⟨6623470995676432088273077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8831294660901909451030769 6623470995676432088273077)
            ·
              refine ⟨620950405844665508275601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6623470995676432088273077 620950405844665508275601)
              ·
                refine ⟨465712804383499131206701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620950405844665508275601 465712804383499131206701)
                ·
                  refine ⟨174642301643812174202513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465712804383499131206701 174642301643812174202513)
                  ·
                    rfl

theorem cell20_382629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_382629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382629 prefixEnd_382629 := by exact prefixLift 382629
  have htrace : WordTrace (prefixWord ++ tailWord_382629) baseStart_382629 baseEnd_382629 := by
    simpa [prefixWord, tailWord_382629, baseEnd_382629] using wordTrace_append hprefix tailTrace_382629
  have hstable : (prefixWord ++ tailWord_382629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382629).length < 2 ^ (prefixWord ++ tailWord_382629).sum := by decide
  have hdescent : baseEnd_382629 < baseStart_382629 := by decide
  rcases family_descends (prefixWord ++ tailWord_382629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382681 : List Nat := [1, 2, 1, 2, 3, 5, 6]
def baseStart_382681 : Nat := 118140960795 + 382681 * 2 ^ 59
def prefixEnd_382681 : Nat := 4983230072969 + 3 ^ 40 * 382681 * 2
def baseEnd_382681 : Nat := 19407337317859011607663

theorem tailTrace_382681 : CollatzResearch.WordTrace tailWord_382681 prefixEnd_382681 19407337317859011607663 := by
  unfold tailWord_382681
  simp only [CollatzResearch.WordTrace]
  refine ⟨13957522726619568556595897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9305015151079712371063931 13957522726619568556595897)
  ·
    refine ⟨10468142044964676417446923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13957522726619568556595897 10468142044964676417446923)
    ·
      refine ⟨15702213067447014626170385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10468142044964676417446923 15702213067447014626170385)
      ·
        refine ⟨11776659800585260969627789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15702213067447014626170385 11776659800585260969627789)
        ·
          refine ⟨4416247425219472863610421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11776659800585260969627789 4416247425219472863610421)
          ·
            refine ⟨414023196114325580963477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4416247425219472863610421 414023196114325580963477)
            ·
              refine ⟨19407337317859011607663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 414023196114325580963477 19407337317859011607663)
              ·
                rfl

theorem cell20_382681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 6].length) (baseStart_382681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382681 prefixEnd_382681 := by exact prefixLift 382681
  have htrace : WordTrace (prefixWord ++ tailWord_382681) baseStart_382681 baseEnd_382681 := by
    simpa [prefixWord, tailWord_382681, baseEnd_382681] using wordTrace_append hprefix tailTrace_382681
  have hstable : (prefixWord ++ tailWord_382681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382681).length < 2 ^ (prefixWord ++ tailWord_382681).sum := by decide
  have hdescent : baseEnd_382681 < baseStart_382681 := by decide
  rcases family_descends (prefixWord ++ tailWord_382681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382688 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_382688 : Nat := 118140960795 + 382688 * 2 ^ 59
def prefixEnd_382688 : Nat := 4983230072969 + 3 ^ 40 * 382688 * 2
def baseEnd_382688 : Nat := 174669230851470191235605

theorem tailTrace_382688 : CollatzResearch.WordTrace tailWord_382688 prefixEnd_382688 174669230851470191235605 := by
  unfold tailWord_382688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978889018797104376050359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9305185358396139168067145 6978889018797104376050359)
  ·
    refine ⟨10468333528195656564075539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6978889018797104376050359 10468333528195656564075539)
    ·
      refine ⟨15702500292293484846113309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10468333528195656564075539 15702500292293484846113309)
      ·
        refine ⟨5888437609610056817292491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15702500292293484846113309 5888437609610056817292491)
        ·
          refine ⟨8832656414415085225938737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5888437609610056817292491 8832656414415085225938737)
          ·
            refine ⟨6624492310811313919454053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8832656414415085225938737 6624492310811313919454053)
            ·
              refine ⟨1242092308277121359897635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6624492310811313919454053 1242092308277121359897635)
              ·
                refine ⟨1863138462415682039846453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242092308277121359897635 1863138462415682039846453)
                ·
                  refine ⟨174669230851470191235605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1863138462415682039846453 174669230851470191235605)
                  ·
                    rfl

theorem cell20_382688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_382688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382688 prefixEnd_382688 := by exact prefixLift 382688
  have htrace : WordTrace (prefixWord ++ tailWord_382688) baseStart_382688 baseEnd_382688 := by
    simpa [prefixWord, tailWord_382688, baseEnd_382688] using wordTrace_append hprefix tailTrace_382688
  have hstable : (prefixWord ++ tailWord_382688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382688).length < 2 ^ (prefixWord ++ tailWord_382688).sum := by decide
  have hdescent : baseEnd_382688 < baseStart_382688 := by decide
  rcases family_descends (prefixWord ++ tailWord_382688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382701 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 3]
def baseStart_382701 : Nat := 118140960795 + 382701 * 2 ^ 59
def prefixEnd_382701 : Nat := 4983230072969 + 3 ^ 40 * 382701 * 2
def baseEnd_382701 : Nat := 174675164405699923802219

theorem tailTrace_382701 : CollatzResearch.WordTrace tailWord_382701 prefixEnd_382701 174675164405699923802219 := by
  unfold tailWord_382701
  simp only [CollatzResearch.WordTrace]
  refine ⟨13958252186547111972323957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9305501457698074648215971 13958252186547111972323957)
  ·
    refine ⟨1308586142488791747405371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13958252186547111972323957 1308586142488791747405371)
    ·
      refine ⟨1962879213733187621108057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308586142488791747405371 1962879213733187621108057)
      ·
        refine ⟨1472159410299890715831043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1962879213733187621108057 1472159410299890715831043)
        ·
          refine ⟨2208239115449836073746565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472159410299890715831043 2208239115449836073746565)
          ·
            refine ⟨414044834146844263827481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2208239115449836073746565 414044834146844263827481)
            ·
              refine ⟨310533625610133197870611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414044834146844263827481 310533625610133197870611)
              ·
                refine ⟨465800438415199796805917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310533625610133197870611 465800438415199796805917)
                ·
                  refine ⟨174675164405699923802219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465800438415199796805917 174675164405699923802219)
                  ·
                    rfl

theorem cell20_382701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_382701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382701 prefixEnd_382701 := by exact prefixLift 382701
  have htrace : WordTrace (prefixWord ++ tailWord_382701) baseStart_382701 baseEnd_382701 := by
    simpa [prefixWord, tailWord_382701, baseEnd_382701] using wordTrace_append hprefix tailTrace_382701
  have hstable : (prefixWord ++ tailWord_382701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382701).length < 2 ^ (prefixWord ++ tailWord_382701).sum := by decide
  have hdescent : baseEnd_382701 < baseStart_382701 := by decide
  rcases family_descends (prefixWord ++ tailWord_382701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382705 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 3]
def baseStart_382705 : Nat := 118140960795 + 382705 * 2 ^ 59
def prefixEnd_382705 : Nat := 4983230072969 + 3 ^ 40 * 382705 * 2
def baseEnd_382705 : Nat := 174676990114693687668869

theorem tailTrace_382705 : CollatzResearch.WordTrace tailWord_382705 prefixEnd_382705 174676990114693687668869 := by
  unfold tailWord_382705
  simp only [CollatzResearch.WordTrace]
  refine ⟨13958398078532620655469569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9305598719021747103646379 13958398078532620655469569)
  ·
    refine ⟨10468798558899465491602177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13958398078532620655469569 10468798558899465491602177)
    ·
      refine ⟨7851598919174599118701633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10468798558899465491602177 7851598919174599118701633)
      ·
        refine ⟨5888699189380949339026225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7851598919174599118701633 5888699189380949339026225)
        ·
          refine ⟨4416524392035712004269669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5888699189380949339026225 4416524392035712004269669)
          ·
            refine ⟨828098323506696000800563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4416524392035712004269669 828098323506696000800563)
            ·
              refine ⟨1242147485260044001200845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828098323506696000800563 1242147485260044001200845)
              ·
                refine ⟨465805306972516500450317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1242147485260044001200845 465805306972516500450317)
                ·
                  refine ⟨174676990114693687668869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465805306972516500450317 174676990114693687668869)
                  ·
                    rfl

theorem cell20_382705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_382705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382705 prefixEnd_382705 := by exact prefixLift 382705
  have htrace : WordTrace (prefixWord ++ tailWord_382705) baseStart_382705 baseEnd_382705 := by
    simpa [prefixWord, tailWord_382705, baseEnd_382705] using wordTrace_append hprefix tailTrace_382705
  have hstable : (prefixWord ++ tailWord_382705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382705).length < 2 ^ (prefixWord ++ tailWord_382705).sum := by decide
  have hdescent : baseEnd_382705 < baseStart_382705 := by decide
  rcases family_descends (prefixWord ++ tailWord_382705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382743 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 3]
def baseStart_382743 : Nat := 118140960795 + 382743 * 2 ^ 59
def prefixEnd_382743 : Nat := 4983230072969 + 3 ^ 40 * 382743 * 2
def baseEnd_382743 : Nat := 174694334350134444402047

theorem tailTrace_382743 : CollatzResearch.WordTrace tailWord_382743 prefixEnd_382743 174694334350134444402047 := by
  unfold tailWord_382743
  simp only [CollatzResearch.WordTrace]
  refine ⟨13959784052394953145352883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9306522701596635430235255 13959784052394953145352883)
  ·
    refine ⟨20939676078592429718029325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13959784052394953145352883 20939676078592429718029325)
    ·
      refine ⟨7852378529472161144260997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20939676078592429718029325 7852378529472161144260997)
      ·
        refine ⟨1472320974276030214548937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7852378529472161144260997 1472320974276030214548937)
        ·
          refine ⟨1104240730707022660911703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1472320974276030214548937 1104240730707022660911703)
          ·
            refine ⟨1656361096060533991367555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104240730707022660911703 1656361096060533991367555)
            ·
              refine ⟨2484541644090800987051333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656361096060533991367555 2484541644090800987051333)
              ·
                refine ⟨465851558267025185072125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2484541644090800987051333 465851558267025185072125)
                ·
                  refine ⟨174694334350134444402047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465851558267025185072125 174694334350134444402047)
                  ·
                    rfl

theorem cell20_382743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 3].length) (baseStart_382743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382743 prefixEnd_382743 := by exact prefixLift 382743
  have htrace : WordTrace (prefixWord ++ tailWord_382743) baseStart_382743 baseEnd_382743 := by
    simpa [prefixWord, tailWord_382743, baseEnd_382743] using wordTrace_append hprefix tailTrace_382743
  have hstable : (prefixWord ++ tailWord_382743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382743).length < 2 ^ (prefixWord ++ tailWord_382743).sum := by decide
  have hdescent : baseEnd_382743 < baseStart_382743 := by decide
  rcases family_descends (prefixWord ++ tailWord_382743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382746 : List Nat := [3, 1, 1, 3, 2, 2, 4, 2, 2]
def baseStart_382746 : Nat := 118140960795 + 382746 * 2 ^ 59
def prefixEnd_382746 : Nat := 4983230072969 + 3 ^ 40 * 382746 * 2
def baseEnd_382746 : Nat := 174695703631879767302035

theorem tailTrace_382746 : CollatzResearch.WordTrace tailWord_382746 prefixEnd_382746 174695703631879767302035 := by
  unfold tailWord_382746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3489973367846021164428023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9306595647589389771808061 3489973367846021164428023)
  ·
    refine ⟨5234960051769031746642035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3489973367846021164428023 5234960051769031746642035)
    ·
      refine ⟨7852440077653547619963053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5234960051769031746642035 7852440077653547619963053)
      ·
        refine ⟨2944665029120080357486145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7852440077653547619963053 2944665029120080357486145)
        ·
          refine ⟨2208498771840060268114609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2944665029120080357486145 2208498771840060268114609)
          ·
            refine ⟨1656374078880045201085957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208498771840060268114609 1656374078880045201085957)
            ·
              refine ⟨310570139790008475203617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1656374078880045201085957 310570139790008475203617)
              ·
                refine ⟨232927604842506356402713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310570139790008475203617 232927604842506356402713)
                ·
                  refine ⟨174695703631879767302035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232927604842506356402713 174695703631879767302035)
                  ·
                    rfl

theorem cell20_382746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_382746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382746 prefixEnd_382746 := by exact prefixLift 382746
  have htrace : WordTrace (prefixWord ++ tailWord_382746) baseStart_382746 baseEnd_382746 := by
    simpa [prefixWord, tailWord_382746, baseEnd_382746] using wordTrace_append hprefix tailTrace_382746
  have hstable : (prefixWord ++ tailWord_382746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382746).length < 2 ^ (prefixWord ++ tailWord_382746).sum := by decide
  have hdescent : baseEnd_382746 < baseStart_382746 := by decide
  rcases family_descends (prefixWord ++ tailWord_382746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382757 : List Nat := [1, 3, 1, 2, 3, 2, 3, 5]
def baseStart_382757 : Nat := 118140960795 + 382757 * 2 ^ 59
def prefixEnd_382757 : Nat := 4983230072969 + 3 ^ 40 * 382757 * 2
def baseEnd_382757 : Nat := 58233574777204205978441

theorem tailTrace_382757 : CollatzResearch.WordTrace tailWord_382757 prefixEnd_382757 58233574777204205978441 := by
  unfold tailWord_382757
  simp only [CollatzResearch.WordTrace]
  refine ⟨13960294674344233536362525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9306863116229489024241683 13960294674344233536362525)
  ·
    refine ⟨5235110502879087576135947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13960294674344233536362525 5235110502879087576135947)
    ·
      refine ⟨7852665754318631364203921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5235110502879087576135947 7852665754318631364203921)
      ·
        refine ⟨5889499315738973523152941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7852665754318631364203921 5889499315738973523152941)
        ·
          refine ⟨2208562243402115071182353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5889499315738973523152941 2208562243402115071182353)
          ·
            refine ⟨1656421682551586303386765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208562243402115071182353 1656421682551586303386765)
            ·
              refine ⟨621158130956844863770037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1656421682551586303386765 621158130956844863770037)
              ·
                refine ⟨58233574777204205978441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 621158130956844863770037 58233574777204205978441)
                ·
                  rfl

theorem cell20_382757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_382757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382757 prefixEnd_382757 := by exact prefixLift 382757
  have htrace : WordTrace (prefixWord ++ tailWord_382757) baseStart_382757 baseEnd_382757 := by
    simpa [prefixWord, tailWord_382757, baseEnd_382757] using wordTrace_append hprefix tailTrace_382757
  have hstable : (prefixWord ++ tailWord_382757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382757).length < 2 ^ (prefixWord ++ tailWord_382757).sum := by decide
  have hdescent : baseEnd_382757 < baseStart_382757 := by decide
  rcases family_descends (prefixWord ++ tailWord_382757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382805 : List Nat := [1, 3, 2, 2, 2, 2, 2, 4, 2]
def baseStart_382805 : Nat := 118140960795 + 382805 * 2 ^ 59
def prefixEnd_382805 : Nat := 4983230072969 + 3 ^ 40 * 382805 * 2
def baseEnd_382805 : Nat := 174722632839537784335127

theorem tailTrace_382805 : CollatzResearch.WordTrace tailWord_382805 prefixEnd_382805 174722632839537784335127 := by
  unfold tailWord_382805
  simp only [CollatzResearch.WordTrace]
  refine ⟨13962045378170337734109869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9308030252113558489406579 13962045378170337734109869)
  ·
    refine ⟨5235767016813876650291201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13962045378170337734109869 5235767016813876650291201)
    ·
      refine ⟨3926825262610407487718401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5235767016813876650291201 3926825262610407487718401)
      ·
        refine ⟨2945118946957805615788801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3926825262610407487718401 2945118946957805615788801)
        ·
          refine ⟨2208839210218354211841601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2945118946957805615788801 2208839210218354211841601)
          ·
            refine ⟨1656629407663765658881201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208839210218354211841601 1656629407663765658881201)
            ·
              refine ⟨1242472055747824244160901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1656629407663765658881201 1242472055747824244160901)
              ·
                refine ⟨232963510452717045780169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1242472055747824244160901 232963510452717045780169)
                ·
                  refine ⟨174722632839537784335127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232963510452717045780169 174722632839537784335127)
                  ·
                    rfl

theorem cell20_382805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_382805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382805 prefixEnd_382805 := by exact prefixLift 382805
  have htrace : WordTrace (prefixWord ++ tailWord_382805) baseStart_382805 baseEnd_382805 := by
    simpa [prefixWord, tailWord_382805, baseEnd_382805] using wordTrace_append hprefix tailTrace_382805
  have hstable : (prefixWord ++ tailWord_382805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382805).length < 2 ^ (prefixWord ++ tailWord_382805).sum := by decide
  have hdescent : baseEnd_382805 < baseStart_382805 := by decide
  rcases family_descends (prefixWord ++ tailWord_382805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382870 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_382870 : Nat := 118140960795 + 382870 * 2 ^ 59
def prefixEnd_382870 : Nat := 4983230072969 + 3 ^ 40 * 382870 * 2
def baseEnd_382870 : Nat := 174752300610686447168195

theorem tailTrace_382870 : CollatzResearch.WordTrace tailWord_382870 prefixEnd_382870 174752300610686447168195 := by
  unfold tailWord_382870
  simp only [CollatzResearch.WordTrace]
  refine ⟨872776007683428364701629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9309610748623235890150709 872776007683428364701629)
  ·
    refine ⟨327291002881285636763111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 872776007683428364701629 327291002881285636763111)
    ·
      refine ⟨490936504321928455144667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327291002881285636763111 490936504321928455144667)
      ·
        refine ⟨736404756482892682717001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490936504321928455144667 736404756482892682717001)
        ·
          refine ⟨552303567362169512037751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736404756482892682717001 552303567362169512037751)
          ·
            refine ⟨828455351043254268056627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552303567362169512037751 828455351043254268056627)
            ·
              refine ⟨1242683026564881402084941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828455351043254268056627 1242683026564881402084941)
              ·
                refine ⟨466006134961830525781853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1242683026564881402084941 466006134961830525781853)
                ·
                  refine ⟨174752300610686447168195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466006134961830525781853 174752300610686447168195)
                  ·
                    rfl

theorem cell20_382870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_382870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382870 prefixEnd_382870 := by exact prefixLift 382870
  have htrace : WordTrace (prefixWord ++ tailWord_382870) baseStart_382870 baseEnd_382870 := by
    simpa [prefixWord, tailWord_382870, baseEnd_382870] using wordTrace_append hprefix tailTrace_382870
  have hstable : (prefixWord ++ tailWord_382870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382870).length < 2 ^ (prefixWord ++ tailWord_382870).sum := by decide
  have hdescent : baseEnd_382870 < baseStart_382870 := by decide
  rcases family_descends (prefixWord ++ tailWord_382870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382871 : List Nat := [1, 1, 3, 3, 1, 4, 2, 5]
def baseStart_382871 : Nat := 118140960795 + 382871 * 2 ^ 59
def prefixEnd_382871 : Nat := 4983230072969 + 3 ^ 40 * 382871 * 2
def baseEnd_382871 : Nat := 58250919012644962711619

theorem tailTrace_382871 : CollatzResearch.WordTrace tailWord_382871 prefixEnd_382871 58250919012644962711619 := by
  unfold tailWord_382871
  simp only [CollatzResearch.WordTrace]
  refine ⟨13964452595931231006012467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9309635063954154004008311 13964452595931231006012467)
  ·
    refine ⟨20946678893896846509018701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13964452595931231006012467 20946678893896846509018701)
    ·
      refine ⟨7855004585211317440882013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20946678893896846509018701 7855004585211317440882013)
      ·
        refine ⟨2945626719454244040330755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7855004585211317440882013 2945626719454244040330755)
        ·
          refine ⟨4418440079181366060496133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2945626719454244040330755 4418440079181366060496133)
          ·
            refine ⟨828457514846506136343025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4418440079181366060496133 828457514846506136343025)
            ·
              refine ⟨621343136134879602257269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828457514846506136343025 621343136134879602257269)
              ·
                refine ⟨58250919012644962711619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 621343136134879602257269 58250919012644962711619)
                ·
                  rfl

theorem cell20_382871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_382871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382871 prefixEnd_382871 := by exact prefixLift 382871
  have htrace : WordTrace (prefixWord ++ tailWord_382871) baseStart_382871 baseEnd_382871 := by
    simpa [prefixWord, tailWord_382871, baseEnd_382871] using wordTrace_append hprefix tailTrace_382871
  have hstable : (prefixWord ++ tailWord_382871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382871).length < 2 ^ (prefixWord ++ tailWord_382871).sum := by decide
  have hdescent : baseEnd_382871 < baseStart_382871 := by decide
  rcases family_descends (prefixWord ++ tailWord_382871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382874 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_382874 : Nat := 118140960795 + 382874 * 2 ^ 59
def prefixEnd_382874 : Nat := 4983230072969 + 3 ^ 40 * 382874 * 2
def baseEnd_382874 : Nat := 174754126319680211034845

theorem tailTrace_382874 : CollatzResearch.WordTrace tailWord_382874 prefixEnd_382874 174754126319680211034845 := by
  unfold tailWord_382874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491140503730090629592919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9309708009946908345581117 3491140503730090629592919)
  ·
    refine ⟨5236710755595135944389379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3491140503730090629592919 5236710755595135944389379)
    ·
      refine ⟨7855066133392703916584069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5236710755595135944389379 7855066133392703916584069)
      ·
        refine ⟨1472824900011131984359513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7855066133392703916584069 1472824900011131984359513)
        ·
          refine ⟨1104618675008348988269635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1472824900011131984359513 1104618675008348988269635)
          ·
            refine ⟨1656928012512523482404453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104618675008348988269635 1656928012512523482404453)
            ·
              refine ⟨310674002346098152950835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1656928012512523482404453 310674002346098152950835)
              ·
                refine ⟨466011003519147229426253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310674002346098152950835 466011003519147229426253)
                ·
                  refine ⟨174754126319680211034845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466011003519147229426253 174754126319680211034845)
                  ·
                    rfl

theorem cell20_382874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_382874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382874 prefixEnd_382874 := by exact prefixLift 382874
  have htrace : WordTrace (prefixWord ++ tailWord_382874) baseStart_382874 baseEnd_382874 := by
    simpa [prefixWord, tailWord_382874, baseEnd_382874] using wordTrace_append hprefix tailTrace_382874
  have hstable : (prefixWord ++ tailWord_382874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382874).length < 2 ^ (prefixWord ++ tailWord_382874).sum := by decide
  have hdescent : baseEnd_382874 < baseStart_382874 := by decide
  rcases family_descends (prefixWord ++ tailWord_382874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382885 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_382885 : Nat := 118140960795 + 382885 * 2 ^ 59
def prefixEnd_382885 : Nat := 4983230072969 + 3 ^ 40 * 382885 * 2
def baseEnd_382885 : Nat := 174759147019413061668133

theorem tailTrace_382885 : CollatzResearch.WordTrace tailWord_382885 prefixEnd_382885 174759147019413061668133 := by
  unfold tailWord_382885
  simp only [CollatzResearch.WordTrace]
  refine ⟨13964963217880511397022109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9309975478587007598014739 13964963217880511397022109)
  ·
    refine ⟨5236861206705191773883291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13964963217880511397022109 5236861206705191773883291)
    ·
      refine ⟨7855291810057787660824937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5236861206705191773883291 7855291810057787660824937)
      ·
        refine ⟨5891468857543340745618703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7855291810057787660824937 5891468857543340745618703)
        ·
          refine ⟨8837203286315011118428055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891468857543340745618703 8837203286315011118428055)
          ·
            refine ⟨13255804929472516677642083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8837203286315011118428055 13255804929472516677642083)
            ·
              refine ⟨19883707394208775016463125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13255804929472516677642083 19883707394208775016463125)
              ·
                refine ⟨932048784103536328896709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19883707394208775016463125 932048784103536328896709)
                ·
                  refine ⟨174759147019413061668133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 932048784103536328896709 174759147019413061668133)
                  ·
                    rfl

theorem cell20_382885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_382885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382885 prefixEnd_382885 := by exact prefixLift 382885
  have htrace : WordTrace (prefixWord ++ tailWord_382885) baseStart_382885 baseEnd_382885 := by
    simpa [prefixWord, tailWord_382885, baseEnd_382885] using wordTrace_append hprefix tailTrace_382885
  have hstable : (prefixWord ++ tailWord_382885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382885).length < 2 ^ (prefixWord ++ tailWord_382885).sum := by decide
  have hdescent : baseEnd_382885 < baseStart_382885 := by decide
  rcases family_descends (prefixWord ++ tailWord_382885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382923 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_382923 : Nat := 118140960795 + 382923 * 2 ^ 59
def prefixEnd_382923 : Nat := 4983230072969 + 3 ^ 40 * 382923 * 2
def baseEnd_382923 : Nat := 174776491254853818401311

theorem tailTrace_382923 : CollatzResearch.WordTrace tailWord_382923 prefixEnd_382923 174776491254853818401311 := by
  unfold tailWord_382923
  simp only [CollatzResearch.WordTrace]
  refine ⟨13966349191742843886905423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9310899461161895924603615 13966349191742843886905423)
  ·
    refine ⟨20949523787614265830358135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13966349191742843886905423 20949523787614265830358135)
    ·
      refine ⟨31424285681421398745537203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20949523787614265830358135 31424285681421398745537203)
      ·
        refine ⟨47136428522132098118305805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31424285681421398745537203 47136428522132098118305805)
        ·
          refine ⟨17676160695799536794364677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47136428522132098118305805 17676160695799536794364677)
          ·
            refine ⟨3314280130462413148943377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17676160695799536794364677 3314280130462413148943377)
            ·
              refine ⟨2485710097846809861707533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3314280130462413148943377 2485710097846809861707533)
              ·
                refine ⟨932141286692553698140325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2485710097846809861707533 932141286692553698140325)
                ·
                  refine ⟨174776491254853818401311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 932141286692553698140325 174776491254853818401311)
                  ·
                    rfl

theorem cell20_382923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_382923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382923 prefixEnd_382923 := by exact prefixLift 382923
  have htrace : WordTrace (prefixWord ++ tailWord_382923) baseStart_382923 baseEnd_382923 := by
    simpa [prefixWord, tailWord_382923, baseEnd_382923] using wordTrace_append hprefix tailTrace_382923
  have hstable : (prefixWord ++ tailWord_382923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382923).length < 2 ^ (prefixWord ++ tailWord_382923).sum := by decide
  have hdescent : baseEnd_382923 < baseStart_382923 := by decide
  rcases family_descends (prefixWord ++ tailWord_382923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382933 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 3]
def baseStart_382933 : Nat := 118140960795 + 382933 * 2 ^ 59
def prefixEnd_382933 : Nat := 4983230072969 + 3 ^ 40 * 382933 * 2
def baseEnd_382933 : Nat := 174781055527338228067937

theorem tailTrace_382933 : CollatzResearch.WordTrace tailWord_382933 prefixEnd_382933 174781055527338228067937 := by
  unfold tailWord_382933
  simp only [CollatzResearch.WordTrace]
  refine ⟨13966713921706615594769453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9311142614471077063179635 13966713921706615594769453)
  ·
    refine ⟨5237517720639980848038545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13966713921706615594769453 5237517720639980848038545)
    ·
      refine ⟨3928138290479985636028909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5237517720639980848038545 3928138290479985636028909)
      ·
        refine ⟨1473051858929994613510841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3928138290479985636028909 1473051858929994613510841)
        ·
          refine ⟨1104788894197495960133131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1473051858929994613510841 1104788894197495960133131)
          ·
            refine ⟨1657183341296243940199697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104788894197495960133131 1657183341296243940199697)
            ·
              refine ⟨1242887505972182955149773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657183341296243940199697 1242887505972182955149773)
              ·
                refine ⟨466082814739568608181165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1242887505972182955149773 466082814739568608181165)
                ·
                  refine ⟨174781055527338228067937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466082814739568608181165 174781055527338228067937)
                  ·
                    rfl

theorem cell20_382933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_382933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382933 prefixEnd_382933 := by exact prefixLift 382933
  have htrace : WordTrace (prefixWord ++ tailWord_382933) baseStart_382933 baseEnd_382933 := by
    simpa [prefixWord, tailWord_382933, baseEnd_382933] using wordTrace_append hprefix tailTrace_382933
  have hstable : (prefixWord ++ tailWord_382933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382933).length < 2 ^ (prefixWord ++ tailWord_382933).sum := by decide
  have hdescent : baseEnd_382933 < baseStart_382933 := by decide
  rcases family_descends (prefixWord ++ tailWord_382933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382954 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_382954 : Nat := 118140960795 + 382954 * 2 ^ 59
def prefixEnd_382954 : Nat := 4983230072969 + 3 ^ 40 * 382954 * 2
def baseEnd_382954 : Nat := 174790640499555488367851

theorem tailTrace_382954 : CollatzResearch.WordTrace tailWord_382954 prefixEnd_382954 174790640499555488367851 := by
  unfold tailWord_382954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491869963657634045320979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9311653236420357454189277 3491869963657634045320979)
  ·
    refine ⟨5237804945486451067981469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3491869963657634045320979 5237804945486451067981469)
    ·
      refine ⟨1964176854557419150493051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5237804945486451067981469 1964176854557419150493051)
      ·
        refine ⟨2946265281836128725739577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964176854557419150493051 2946265281836128725739577)
        ·
          refine ⟨2209698961377096544304683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2946265281836128725739577 2209698961377096544304683)
          ·
            refine ⟨3314548442065644816457025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209698961377096544304683 3314548442065644816457025)
            ·
              refine ⟨2485911331549233612342769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3314548442065644816457025 2485911331549233612342769)
              ·
                refine ⟨1864433498661925209257077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2485911331549233612342769 1864433498661925209257077)
                ·
                  refine ⟨174790640499555488367851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1864433498661925209257077 174790640499555488367851)
                  ·
                    rfl

theorem cell20_382954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_382954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382954 prefixEnd_382954 := by exact prefixLift 382954
  have htrace : WordTrace (prefixWord ++ tailWord_382954) baseStart_382954 baseEnd_382954 := by
    simpa [prefixWord, tailWord_382954, baseEnd_382954] using wordTrace_append hprefix tailTrace_382954
  have hstable : (prefixWord ++ tailWord_382954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382954).length < 2 ^ (prefixWord ++ tailWord_382954).sum := by decide
  have hdescent : baseEnd_382954 < baseStart_382954 := by decide
  rcases family_descends (prefixWord ++ tailWord_382954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382974 : List Nat := [4, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_382974 : Nat := 118140960795 + 382974 * 2 ^ 59
def prefixEnd_382974 : Nat := 4983230072969 + 3 ^ 40 * 382974 * 2
def baseEnd_382974 : Nat := 174799769044524307701103

theorem tailTrace_382974 : CollatzResearch.WordTrace tailWord_382974 prefixEnd_382974 174799769044524307701103 := by
  unfold tailWord_382974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1746026164319759949626497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9312139543038719731341317 1746026164319759949626497)
  ·
    refine ⟨1309519623239819962219873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1746026164319759949626497 1309519623239819962219873)
    ·
      refine ⟨982139717429864971664905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1309519623239819962219873 982139717429864971664905)
      ·
        refine ⟨736604788072398728748679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 982139717429864971664905 736604788072398728748679)
        ·
          refine ⟨1104907182108598093123019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736604788072398728748679 1104907182108598093123019)
          ·
            refine ⟨1657360773162897139684529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104907182108598093123019 1657360773162897139684529)
            ·
              refine ⟨1243020579872172854763397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657360773162897139684529 1243020579872172854763397)
              ·
                refine ⟨233066358726032410268137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1243020579872172854763397 233066358726032410268137)
                ·
                  refine ⟨174799769044524307701103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233066358726032410268137 174799769044524307701103)
                  ·
                    rfl

theorem cell20_382974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_382974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_382974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_382974 prefixEnd_382974 := by exact prefixLift 382974
  have htrace : WordTrace (prefixWord ++ tailWord_382974) baseStart_382974 baseEnd_382974 := by
    simpa [prefixWord, tailWord_382974, baseEnd_382974] using wordTrace_append hprefix tailTrace_382974
  have hstable : (prefixWord ++ tailWord_382974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382974).length < 2 ^ (prefixWord ++ tailWord_382974).sum := by decide
  have hdescent : baseEnd_382974 < baseStart_382974 := by decide
  rcases family_descends (prefixWord ++ tailWord_382974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383002 : List Nat := [3, 1, 1, 3, 1, 5, 2, 4]
def baseStart_383002 : Nat := 118140960795 + 383002 * 2 ^ 59
def prefixEnd_383002 : Nat := 4983230072969 + 3 ^ 40 * 383002 * 2
def baseEnd_383002 : Nat := 58270849669160218255885

theorem tailTrace_383002 : CollatzResearch.WordTrace tailWord_383002 prefixEnd_383002 58270849669160218255885 := by
  unfold tailWord_383002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3492307639614160094757815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9312820372304426919354173 3492307639614160094757815)
  ·
    refine ⟨5238461459421240142136723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3492307639614160094757815 5238461459421240142136723)
    ·
      refine ⟨7857692189131860213205085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5238461459421240142136723 7857692189131860213205085)
      ·
        refine ⟨2946634570924447579951907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7857692189131860213205085 2946634570924447579951907)
        ·
          refine ⟨4419951856386671369927861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2946634570924447579951907 4419951856386671369927861)
          ·
            refine ⟨414370486536250440930737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4419951856386671369927861 414370486536250440930737)
            ·
              refine ⟨310777864902187830698053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414370486536250440930737 310777864902187830698053)
              ·
                refine ⟨58270849669160218255885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310777864902187830698053 58270849669160218255885)
                ·
                  rfl

theorem cell20_383002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_383002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383002 prefixEnd_383002 := by exact prefixLift 383002
  have htrace : WordTrace (prefixWord ++ tailWord_383002) baseStart_383002 baseEnd_383002 := by
    simpa [prefixWord, tailWord_383002, baseEnd_383002] using wordTrace_append hprefix tailTrace_383002
  have hstable : (prefixWord ++ tailWord_383002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383002).length < 2 ^ (prefixWord ++ tailWord_383002).sum := by decide
  have hdescent : baseEnd_383002 < baseStart_383002 := by decide
  rcases family_descends (prefixWord ++ tailWord_383002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383033 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 4]
def baseStart_383033 : Nat := 118140960795 + 383033 * 2 ^ 59
def prefixEnd_383033 : Nat := 4983230072969 + 3 ^ 40 * 383033 * 2
def baseEnd_383033 : Nat := 174826698252182324734195

theorem tailTrace_383033 : CollatzResearch.WordTrace tailWord_383033 prefixEnd_383033 174826698252182324734195 := by
  unfold tailWord_383033
  simp only [CollatzResearch.WordTrace]
  refine ⟨13970361221344332673409753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9313574147562888448939835 13970361221344332673409753)
  ·
    refine ⟨10477770916008249505057315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13970361221344332673409753 10477770916008249505057315)
    ·
      refine ⟨15716656374012374257585973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10477770916008249505057315 15716656374012374257585973)
      ·
        refine ⟨1473436535063660086648685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15716656374012374257585973 1473436535063660086648685)
        ·
          refine ⟨552538700648872532493257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1473436535063660086648685 552538700648872532493257)
          ·
            refine ⟨414404025486654399369943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552538700648872532493257 414404025486654399369943)
            ·
              refine ⟨621606038229981599054915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414404025486654399369943 621606038229981599054915)
              ·
                refine ⟨932409057344972398582373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621606038229981599054915 932409057344972398582373)
                ·
                  refine ⟨174826698252182324734195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 932409057344972398582373 174826698252182324734195)
                  ·
                    rfl

theorem cell20_383033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_383033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383033 prefixEnd_383033 := by exact prefixLift 383033
  have htrace : WordTrace (prefixWord ++ tailWord_383033) baseStart_383033 baseEnd_383033 := by
    simpa [prefixWord, tailWord_383033, baseEnd_383033] using wordTrace_append hprefix tailTrace_383033
  have hstable : (prefixWord ++ tailWord_383033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383033).length < 2 ^ (prefixWord ++ tailWord_383033).sum := by decide
  have hdescent : baseEnd_383033 < baseStart_383033 := by decide
  rcases family_descends (prefixWord ++ tailWord_383033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383082 : List Nat := [3, 1, 3, 2, 11]
def baseStart_383082 : Nat := 118140960795 + 383082 * 2 ^ 59
def prefixEnd_383082 : Nat := 4983230072969 + 3 ^ 40 * 383082 * 2
def baseEnd_383082 : Nat := 2158630409720443606181

theorem tailTrace_383082 : CollatzResearch.WordTrace tailWord_383082 prefixEnd_383082 2158630409720443606181 := by
  unfold tailWord_383082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3493037099541703510485875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9314765598777876027962333 3493037099541703510485875)
  ·
    refine ⟨5239555649312555265728813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3493037099541703510485875 5239555649312555265728813)
    ·
      refine ⟨1964833368492208224648305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5239555649312555265728813 1964833368492208224648305)
      ·
        refine ⟨1473625026369156168486229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1964833368492208224648305 1473625026369156168486229)
        ·
          refine ⟨2158630409720443606181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1473625026369156168486229 2158630409720443606181)
          ·
            rfl

theorem cell20_383082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 11].length) (baseStart_383082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383082 prefixEnd_383082 := by exact prefixLift 383082
  have htrace : WordTrace (prefixWord ++ tailWord_383082) baseStart_383082 baseEnd_383082 := by
    simpa [prefixWord, tailWord_383082, baseEnd_383082] using wordTrace_append hprefix tailTrace_383082
  have hstable : (prefixWord ++ tailWord_383082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383082).length < 2 ^ (prefixWord ++ tailWord_383082).sum := by decide
  have hdescent : baseEnd_383082 < baseStart_383082 := by decide
  rcases family_descends (prefixWord ++ tailWord_383082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383085 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 3]
def baseStart_383085 : Nat := 118140960795 + 383085 * 2 ^ 59
def prefixEnd_383085 : Nat := 4983230072969 + 3 ^ 40 * 383085 * 2
def baseEnd_383085 : Nat := 174850432469101255000649

theorem tailTrace_383085 : CollatzResearch.WordTrace tailWord_383085 prefixEnd_383085 174850432469101255000649 := by
  unfold tailWord_383085
  simp only [CollatzResearch.WordTrace]
  refine ⟨13972257817155945554302709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9314838544770630369535139 13972257817155945554302709)
  ·
    refine ⟨1309899170358369895715879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13972257817155945554302709 1309899170358369895715879)
    ·
      refine ⟨1964848755537554843573819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309899170358369895715879 1964848755537554843573819)
      ·
        refine ⟨2947273133306332265360729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964848755537554843573819 2947273133306332265360729)
        ·
          refine ⟨2210454849979749199020547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2947273133306332265360729 2210454849979749199020547)
          ·
            refine ⟨3315682274969623798530821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210454849979749199020547 3315682274969623798530821)
            ·
              refine ⟨621690426556804462224529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3315682274969623798530821 621690426556804462224529)
              ·
                refine ⟨466267819917603346668397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621690426556804462224529 466267819917603346668397)
                ·
                  refine ⟨174850432469101255000649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466267819917603346668397 174850432469101255000649)
                  ·
                    rfl

theorem cell20_383085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_383085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383085 prefixEnd_383085 := by exact prefixLift 383085
  have htrace : WordTrace (prefixWord ++ tailWord_383085) baseStart_383085 baseEnd_383085 := by
    simpa [prefixWord, tailWord_383085, baseEnd_383085] using wordTrace_append hprefix tailTrace_383085
  have hstable : (prefixWord ++ tailWord_383085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383085).length < 2 ^ (prefixWord ++ tailWord_383085).sum := by decide
  have hdescent : baseEnd_383085 < baseStart_383085 := by decide
  rcases family_descends (prefixWord ++ tailWord_383085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383088 : List Nat := [2, 1, 1, 1, 5, 4, 2, 2, 2]
def baseStart_383088 : Nat := 118140960795 + 383088 * 2 ^ 59
def prefixEnd_383088 : Nat := 4983230072969 + 3 ^ 40 * 383088 * 2
def baseEnd_383088 : Nat := 174851801750846577900637

theorem tailTrace_383088 : CollatzResearch.WordTrace tailWord_383088 prefixEnd_383088 174851801750846577900637 := by
  unfold tailWord_383088
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986183618072538533330959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9314911490763384711107945 6986183618072538533330959)
  ·
    refine ⟨10479275427108807799996439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6986183618072538533330959 10479275427108807799996439)
    ·
      refine ⟨15718913140663211699994659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10479275427108807799996439 15718913140663211699994659)
      ·
        refine ⟨23578369710994817549991989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15718913140663211699994659 23578369710994817549991989)
        ·
          refine ⟨2210472160405764145311749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23578369710994817549991989 2210472160405764145311749)
          ·
            refine ⟨414463530076080777245953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2210472160405764145311749 414463530076080777245953)
            ·
              refine ⟨310847647557060582934465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414463530076080777245953 310847647557060582934465)
              ·
                refine ⟨233135735667795437200849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310847647557060582934465 233135735667795437200849)
                ·
                  refine ⟨174851801750846577900637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233135735667795437200849 174851801750846577900637)
                  ·
                    rfl

theorem cell20_383088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_383088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383088 prefixEnd_383088 := by exact prefixLift 383088
  have htrace : WordTrace (prefixWord ++ tailWord_383088) baseStart_383088 baseEnd_383088 := by
    simpa [prefixWord, tailWord_383088, baseEnd_383088] using wordTrace_append hprefix tailTrace_383088
  have hstable : (prefixWord ++ tailWord_383088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383088).length < 2 ^ (prefixWord ++ tailWord_383088).sum := by decide
  have hdescent : baseEnd_383088 < baseStart_383088 := by decide
  rcases family_descends (prefixWord ++ tailWord_383088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383113 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_383113 : Nat := 118140960795 + 383113 * 2 ^ 59
def prefixEnd_383113 : Nat := 4983230072969 + 3 ^ 40 * 383113 * 2
def baseEnd_383113 : Nat := 174863212432057602067201

theorem tailTrace_383113 : CollatzResearch.WordTrace tailWord_383113 prefixEnd_383113 174863212432057602067201 := by
  unfold tailWord_383113
  simp only [CollatzResearch.WordTrace]
  refine ⟨13973279061054506336321993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9315519374036337557547995 13973279061054506336321993)
  ·
    refine ⟨10479959295790879752241495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13973279061054506336321993 10479959295790879752241495)
    ·
      refine ⟨15719938943686319628362243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10479959295790879752241495 15719938943686319628362243)
      ·
        refine ⟨23579908415529479442543365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15719938943686319628362243 23579908415529479442543365)
        ·
          refine ⟨4421232827911777395476881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23579908415529479442543365 4421232827911777395476881)
          ·
            refine ⟨3315924620933833046607661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4421232827911777395476881 3315924620933833046607661)
            ·
              refine ⟨1243471732850187392477873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3315924620933833046607661 1243471732850187392477873)
              ·
                refine ⟨932603799637640544358405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1243471732850187392477873 932603799637640544358405)
                ·
                  refine ⟨174863212432057602067201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 932603799637640544358405 174863212432057602067201)
                  ·
                    rfl

theorem cell20_383113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_383113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383113 prefixEnd_383113 := by exact prefixLift 383113
  have htrace : WordTrace (prefixWord ++ tailWord_383113) baseStart_383113 baseEnd_383113 := by
    simpa [prefixWord, tailWord_383113, baseEnd_383113] using wordTrace_append hprefix tailTrace_383113
  have hstable : (prefixWord ++ tailWord_383113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383113).length < 2 ^ (prefixWord ++ tailWord_383113).sum := by decide
  have hdescent : baseEnd_383113 < baseStart_383113 := by decide
  rcases family_descends (prefixWord ++ tailWord_383113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383140 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 3]
def baseStart_383140 : Nat := 118140960795 + 383140 * 2 ^ 59
def prefixEnd_383140 : Nat := 4983230072969 + 3 ^ 40 * 383140 * 2
def baseEnd_383140 : Nat := 174875535967765508167091

theorem tailTrace_383140 : CollatzResearch.WordTrace tailWord_383140 prefixEnd_383140 174875535967765508167091 := by
  unfold tailWord_383140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987131915978344973777437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9316175887971126631703249 6987131915978344973777437)
  ·
    refine ⟨2620174468491879365166539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6987131915978344973777437 2620174468491879365166539)
    ·
      refine ⟨3930261702737819047749809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2620174468491879365166539 3930261702737819047749809)
      ·
        refine ⟨2947696277053364285812357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3930261702737819047749809 2947696277053364285812357)
        ·
          refine ⟨552693051947505803589817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2947696277053364285812357 552693051947505803589817)
          ·
            refine ⟨414519788960629352692363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552693051947505803589817 414519788960629352692363)
            ·
              refine ⟨621779683440944029038545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414519788960629352692363 621779683440944029038545)
              ·
                refine ⟨466334762580708021778909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621779683440944029038545 466334762580708021778909)
                ·
                  refine ⟨174875535967765508167091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466334762580708021778909 174875535967765508167091)
                  ·
                    rfl

theorem cell20_383140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_383140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383140 prefixEnd_383140 := by exact prefixLift 383140
  have htrace : WordTrace (prefixWord ++ tailWord_383140) baseStart_383140 baseEnd_383140 := by
    simpa [prefixWord, tailWord_383140, baseEnd_383140] using wordTrace_append hprefix tailTrace_383140
  have hstable : (prefixWord ++ tailWord_383140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383140).length < 2 ^ (prefixWord ++ tailWord_383140).sum := by decide
  have hdescent : baseEnd_383140 < baseStart_383140 := by decide
  rcases family_descends (prefixWord ++ tailWord_383140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383157 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 3]
def baseStart_383157 : Nat := 118140960795 + 383157 * 2 ^ 59
def prefixEnd_383157 : Nat := 4983230072969 + 3 ^ 40 * 383157 * 2
def baseEnd_383157 : Nat := 174883295230989004600355

theorem tailTrace_383157 : CollatzResearch.WordTrace tailWord_383157 prefixEnd_383157 174883295230989004600355 := by
  unfold tailWord_383157
  simp only [CollatzResearch.WordTrace]
  refine ⟨13974883872895101850923725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9316589248596734567282483 13974883872895101850923725)
  ·
    refine ⟨5240581452335663194096397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13974883872895101850923725 5240581452335663194096397)
    ·
      refine ⟨1965218044625873697786149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5240581452335663194096397 1965218044625873697786149)
      ·
        refine ⟨368478383367351318334903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1965218044625873697786149 368478383367351318334903)
        ·
          refine ⟨552717575051026977502355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368478383367351318334903 552717575051026977502355)
          ·
            refine ⟨829076362576540466253533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552717575051026977502355 829076362576540466253533)
            ·
              refine ⟨310903635966202674845075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 829076362576540466253533 310903635966202674845075)
              ·
                refine ⟨466355453949304012267613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310903635966202674845075 466355453949304012267613)
                ·
                  refine ⟨174883295230989004600355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466355453949304012267613 174883295230989004600355)
                  ·
                    rfl

theorem cell20_383157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_383157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383157 prefixEnd_383157 := by exact prefixLift 383157
  have htrace : WordTrace (prefixWord ++ tailWord_383157) baseStart_383157 baseEnd_383157 := by
    simpa [prefixWord, tailWord_383157, baseEnd_383157] using wordTrace_append hprefix tailTrace_383157
  have hstable : (prefixWord ++ tailWord_383157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383157).length < 2 ^ (prefixWord ++ tailWord_383157).sum := by decide
  have hdescent : baseEnd_383157 < baseStart_383157 := by decide
  rcases family_descends (prefixWord ++ tailWord_383157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383161 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 3]
def baseStart_383161 : Nat := 118140960795 + 383161 * 2 ^ 59
def prefixEnd_383161 : Nat := 4983230072969 + 3 ^ 40 * 383161 * 2
def baseEnd_383161 : Nat := 174885120939982768467005

theorem tailTrace_383161 : CollatzResearch.WordTrace tailWord_383161 prefixEnd_383161 174885120939982768467005 := by
  unfold tailWord_383161
  simp only [CollatzResearch.WordTrace]
  refine ⟨13975029764880610534069337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9316686509920407022712891 13975029764880610534069337)
  ·
    refine ⟨10481272323660457900552003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13975029764880610534069337 10481272323660457900552003)
    ·
      refine ⟨15721908485490686850828005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10481272323660457900552003 15721908485490686850828005)
      ·
        refine ⟨2947857841029503784530251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15721908485490686850828005 2947857841029503784530251)
        ·
          refine ⟨4421786761544255676795377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2947857841029503784530251 4421786761544255676795377)
          ·
            refine ⟨3316340071158191757596533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4421786761544255676795377 3316340071158191757596533)
            ·
              refine ⟨310906881671080477274675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3316340071158191757596533 310906881671080477274675)
              ·
                refine ⟨466360322506620715912013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310906881671080477274675 466360322506620715912013)
                ·
                  refine ⟨174885120939982768467005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466360322506620715912013 174885120939982768467005)
                  ·
                    rfl

theorem cell20_383161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_383161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383161 prefixEnd_383161 := by exact prefixLift 383161
  have htrace : WordTrace (prefixWord ++ tailWord_383161) baseStart_383161 baseEnd_383161 := by
    simpa [prefixWord, tailWord_383161, baseEnd_383161] using wordTrace_append hprefix tailTrace_383161
  have hstable : (prefixWord ++ tailWord_383161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383161).length < 2 ^ (prefixWord ++ tailWord_383161).sum := by decide
  have hdescent : baseEnd_383161 < baseStart_383161 := by decide
  rcases family_descends (prefixWord ++ tailWord_383161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383182 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_383182 : Nat := 118140960795 + 383182 * 2 ^ 59
def prefixEnd_383182 : Nat := 4983230072969 + 3 ^ 40 * 383182 * 2
def baseEnd_383182 : Nat := 174894705912200028766919

theorem tailTrace_383182 : CollatzResearch.WordTrace tailWord_383182 prefixEnd_383182 174894705912200028766919 := by
  unfold tailWord_383182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1746974462225566390072975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9317197131869687413722533 1746974462225566390072975)
  ·
    refine ⟨2620461693338349585109463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1746974462225566390072975 2620461693338349585109463)
    ·
      refine ⟨3930692540007524377664195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2620461693338349585109463 3930692540007524377664195)
      ·
        refine ⟨5896038810011286566496293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3930692540007524377664195 5896038810011286566496293)
        ·
          refine ⟨1105507276877116231218055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5896038810011286566496293 1105507276877116231218055)
          ·
            refine ⟨1658260915315674346827083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105507276877116231218055 1658260915315674346827083)
            ·
              refine ⟨2487391372973511520240625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658260915315674346827083 2487391372973511520240625)
              ·
                refine ⟨1865543529730133640180469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2487391372973511520240625 1865543529730133640180469)
                ·
                  refine ⟨174894705912200028766919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1865543529730133640180469 174894705912200028766919)
                  ·
                    rfl

theorem cell20_383182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_383182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383182 prefixEnd_383182 := by exact prefixLift 383182
  have htrace : WordTrace (prefixWord ++ tailWord_383182) baseStart_383182 baseEnd_383182 := by
    simpa [prefixWord, tailWord_383182, baseEnd_383182] using wordTrace_append hprefix tailTrace_383182
  have hstable : (prefixWord ++ tailWord_383182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383182).length < 2 ^ (prefixWord ++ tailWord_383182).sum := by decide
  have hdescent : baseEnd_383182 < baseStart_383182 := by decide
  rcases family_descends (prefixWord ++ tailWord_383182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383244 : List Nat := [2, 2, 1, 2, 2, 2, 2, 5, 2]
def baseStart_383244 : Nat := 118140960795 + 383244 * 2 ^ 59
def prefixEnd_383244 : Nat := 4983230072969 + 3 ^ 40 * 383244 * 2
def baseEnd_383244 : Nat := 174923004401603368699999

theorem tailTrace_383244 : CollatzResearch.WordTrace tailWord_383244 prefixEnd_383244 174923004401603368699999 := by
  unfold tailWord_383244
  simp only [CollatzResearch.WordTrace]
  refine ⟨6989028511789957854670393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9318704682386610472893857 6989028511789957854670393)
  ·
    refine ⟨5241771383842468391002795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6989028511789957854670393 5241771383842468391002795)
    ·
      refine ⟨7862657075763702586504193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241771383842468391002795 7862657075763702586504193)
      ·
        refine ⟨5896992806822776939878145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7862657075763702586504193 5896992806822776939878145)
        ·
          refine ⟨4422744605117082704908609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5896992806822776939878145 4422744605117082704908609)
          ·
            refine ⟨3317058453837812028681457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4422744605117082704908609 3317058453837812028681457)
            ·
              refine ⟨2487793840378359021511093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3317058453837812028681457 2487793840378359021511093)
              ·
                refine ⟨233230672535471158266665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2487793840378359021511093 233230672535471158266665)
                ·
                  refine ⟨174923004401603368699999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233230672535471158266665 174923004401603368699999)
                  ·
                    rfl

theorem cell20_383244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_383244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383244 prefixEnd_383244 := by exact prefixLift 383244
  have htrace : WordTrace (prefixWord ++ tailWord_383244) baseStart_383244 baseEnd_383244 := by
    simpa [prefixWord, tailWord_383244, baseEnd_383244] using wordTrace_append hprefix tailTrace_383244
  have hstable : (prefixWord ++ tailWord_383244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383244).length < 2 ^ (prefixWord ++ tailWord_383244).sum := by decide
  have hdescent : baseEnd_383244 < baseStart_383244 := by decide
  rcases family_descends (prefixWord ++ tailWord_383244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383282 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_383282 : Nat := 118140960795 + 383282 * 2 ^ 59
def prefixEnd_383282 : Nat := 4983230072969 + 3 ^ 40 * 383282 * 2
def baseEnd_383282 : Nat := 174940348637044125433177

theorem tailTrace_383282 : CollatzResearch.WordTrace tailWord_383282 prefixEnd_383282 174940348637044125433177 := by
  unfold tailWord_383282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494860749360562049806025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9319628664961498799482733 3494860749360562049806025)
  ·
    refine ⟨2621145562020421537354519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3494860749360562049806025 2621145562020421537354519)
    ·
      refine ⟨3931718343030632306031779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621145562020421537354519 3931718343030632306031779)
      ·
        refine ⟨5897577514545948459047669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3931718343030632306031779 5897577514545948459047669)
        ·
          refine ⟨552897891988682668035719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5897577514545948459047669 552897891988682668035719)
          ·
            refine ⟨829346837983024002053579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552897891988682668035719 829346837983024002053579)
            ·
              refine ⟨1244020256974536003080369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829346837983024002053579 1244020256974536003080369)
              ·
                refine ⟨933015192730902002310277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244020256974536003080369 933015192730902002310277)
                ·
                  refine ⟨174940348637044125433177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933015192730902002310277 174940348637044125433177)
                  ·
                    rfl

theorem cell20_383282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_383282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383282 prefixEnd_383282 := by exact prefixLift 383282
  have htrace : WordTrace (prefixWord ++ tailWord_383282) baseStart_383282 baseEnd_383282 := by
    simpa [prefixWord, tailWord_383282, baseEnd_383282] using wordTrace_append hprefix tailTrace_383282
  have hstable : (prefixWord ++ tailWord_383282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383282).length < 2 ^ (prefixWord ++ tailWord_383282).sum := by decide
  have hdescent : baseEnd_383282 < baseStart_383282 := by decide
  rcases family_descends (prefixWord ++ tailWord_383282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383313 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 3]
def baseStart_383313 : Nat := 118140960795 + 383313 * 2 ^ 59
def prefixEnd_383313 : Nat := 4983230072969 + 3 ^ 40 * 383313 * 2
def baseEnd_383313 : Nat := 174954497881745795399717

theorem tailTrace_383313 : CollatzResearch.WordTrace tailWord_383313 prefixEnd_383313 174954497881745795399717 := by
  unfold tailWord_383313
  simp only [CollatzResearch.WordTrace]
  refine ⟨13980573660329940493602593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9320382440219960329068395 13980573660329940493602593)
  ·
    refine ⟨10485430245247455370201945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13980573660329940493602593 10485430245247455370201945)
    ·
      refine ⟨7864072683935591527651459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10485430245247455370201945 7864072683935591527651459)
      ·
        refine ⟨11796109025903387291477189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7864072683935591527651459 11796109025903387291477189)
        ·
          refine ⟨2211770442356885117151973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11796109025903387291477189 2211770442356885117151973)
          ·
            refine ⟨414706957941915959465995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2211770442356885117151973 414706957941915959465995)
            ·
              refine ⟨622060436912873939198993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414706957941915959465995 622060436912873939198993)
              ·
                refine ⟨466545327684655454399245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622060436912873939198993 466545327684655454399245)
                ·
                  refine ⟨174954497881745795399717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466545327684655454399245 174954497881745795399717)
                  ·
                    rfl

theorem cell20_383313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_383313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383313 prefixEnd_383313 := by exact prefixLift 383313
  have htrace : WordTrace (prefixWord ++ tailWord_383313) baseStart_383313 baseEnd_383313 := by
    simpa [prefixWord, tailWord_383313, baseEnd_383313] using wordTrace_append hprefix tailTrace_383313
  have hstable : (prefixWord ++ tailWord_383313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383313).length < 2 ^ (prefixWord ++ tailWord_383313).sum := by decide
  have hdescent : baseEnd_383313 < baseStart_383313 := by decide
  rcases family_descends (prefixWord ++ tailWord_383313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383330 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_383330 : Nat := 118140960795 + 383330 * 2 ^ 59
def prefixEnd_383330 : Nat := 4983230072969 + 3 ^ 40 * 383330 * 2
def baseEnd_383330 : Nat := 174962257144969291832981

theorem tailTrace_383330 : CollatzResearch.WordTrace tailWord_383330 prefixEnd_383330 174962257144969291832981 := by
  unfold tailWord_383330
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495298425317088099242861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9320795800845568264647629 3495298425317088099242861)
  ·
    refine ⟨1310736909493908037216073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3495298425317088099242861 1310736909493908037216073)
    ·
      refine ⟨983052682120431027912055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1310736909493908037216073 983052682120431027912055)
      ·
        refine ⟨1474579023180646541868083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983052682120431027912055 1474579023180646541868083)
        ·
          refine ⟨2211868534770969812802125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474579023180646541868083 2211868534770969812802125)
          ·
            refine ⟨829450700539113679800797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2211868534770969812802125 829450700539113679800797)
            ·
              refine ⟨311044012702167629925299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 829450700539113679800797 311044012702167629925299)
              ·
                refine ⟨466566019053251444887949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311044012702167629925299 466566019053251444887949)
                ·
                  refine ⟨174962257144969291832981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466566019053251444887949 174962257144969291832981)
                  ·
                    rfl

theorem cell20_383330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_383330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383330 prefixEnd_383330 := by exact prefixLift 383330
  have htrace : WordTrace (prefixWord ++ tailWord_383330) baseStart_383330 baseEnd_383330 := by
    simpa [prefixWord, tailWord_383330, baseEnd_383330] using wordTrace_append hprefix tailTrace_383330
  have hstable : (prefixWord ++ tailWord_383330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383330).length < 2 ^ (prefixWord ++ tailWord_383330).sum := by decide
  have hdescent : baseEnd_383330 < baseStart_383330 := by decide
  rcases family_descends (prefixWord ++ tailWord_383330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383341 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_383341 : Nat := 118140960795 + 383341 * 2 ^ 59
def prefixEnd_383341 : Nat := 4983230072969 + 3 ^ 40 * 383341 * 2
def baseEnd_383341 : Nat := 174967277844702142466269

theorem tailTrace_383341 : CollatzResearch.WordTrace tailWord_383341 prefixEnd_383341 174967277844702142466269 := by
  unfold tailWord_383341
  simp only [CollatzResearch.WordTrace]
  refine ⟨13981594904228501275621877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9321063269485667517081251 13981594904228501275621877)
  ·
    refine ⟨1310774522271421994589551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13981594904228501275621877 1310774522271421994589551)
    ·
      refine ⟨1966161783407132991884327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1310774522271421994589551 1966161783407132991884327)
      ·
        refine ⟨2949242675110699487826491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1966161783407132991884327 2949242675110699487826491)
        ·
          refine ⟨4423864012666049231739737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949242675110699487826491 4423864012666049231739737)
          ·
            refine ⟨3317898009499536923804803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4423864012666049231739737 3317898009499536923804803)
            ·
              refine ⟨4976847014249305385707205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317898009499536923804803 4976847014249305385707205)
              ·
                refine ⟨933158815171744759820101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4976847014249305385707205 933158815171744759820101)
                ·
                  refine ⟨174967277844702142466269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933158815171744759820101 174967277844702142466269)
                  ·
                    rfl

theorem cell20_383341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_383341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383341 prefixEnd_383341 := by exact prefixLift 383341
  have htrace : WordTrace (prefixWord ++ tailWord_383341) baseStart_383341 baseEnd_383341 := by
    simpa [prefixWord, tailWord_383341, baseEnd_383341] using wordTrace_append hprefix tailTrace_383341
  have hstable : (prefixWord ++ tailWord_383341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383341).length < 2 ^ (prefixWord ++ tailWord_383341).sum := by decide
  have hdescent : baseEnd_383341 < baseStart_383341 := by decide
  rcases family_descends (prefixWord ++ tailWord_383341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383350 : List Nat := [5, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_383350 : Nat := 118140960795 + 383350 * 2 ^ 59
def prefixEnd_383350 : Nat := 4983230072969 + 3 ^ 40 * 383350 * 2
def baseEnd_383350 : Nat := 174971385689938111166233

theorem tailTrace_383350 : CollatzResearch.WordTrace tailWord_383350 prefixEnd_383350 174971385689938111166233 := by
  unfold tailWord_383350
  simp only [CollatzResearch.WordTrace]
  refine ⟨873870197574743488293719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9321282107463930541799669 873870197574743488293719)
  ·
    refine ⟨1310805296362115232440579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 873870197574743488293719 1310805296362115232440579)
    ·
      refine ⟨1966207944543172848660869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1310805296362115232440579 1966207944543172848660869)
      ·
        refine ⟨368663989601844909123913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1966207944543172848660869 368663989601844909123913)
        ·
          refine ⟨276497992201383681842935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368663989601844909123913 276497992201383681842935)
          ·
            refine ⟨414746988302075522764403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276497992201383681842935 414746988302075522764403)
            ·
              refine ⟨622120482453113284146605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414746988302075522764403 622120482453113284146605)
              ·
                refine ⟨233295180919917481554977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622120482453113284146605 233295180919917481554977)
                ·
                  refine ⟨174971385689938111166233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233295180919917481554977 174971385689938111166233)
                  ·
                    rfl

theorem cell20_383350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_383350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383350 prefixEnd_383350 := by exact prefixLift 383350
  have htrace : WordTrace (prefixWord ++ tailWord_383350) baseStart_383350 baseEnd_383350 := by
    simpa [prefixWord, tailWord_383350, baseEnd_383350] using wordTrace_append hprefix tailTrace_383350
  have hstable : (prefixWord ++ tailWord_383350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383350).length < 2 ^ (prefixWord ++ tailWord_383350).sum := by decide
  have hdescent : baseEnd_383350 < baseStart_383350 := by decide
  rcases family_descends (prefixWord ++ tailWord_383350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383355 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_383355 : Nat := 118140960795 + 383355 * 2 ^ 59
def prefixEnd_383355 : Nat := 4983230072969 + 3 ^ 40 * 383355 * 2
def baseEnd_383355 : Nat := 174973667826180315999545

theorem tailTrace_383355 : CollatzResearch.WordTrace tailWord_383355 prefixEnd_383355 174973667826180315999545 := by
  unfold tailWord_383355
  simp only [CollatzResearch.WordTrace]
  refine ⟨13982105526177781666631519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9321403684118521111087679 13982105526177781666631519)
  ·
    refine ⟨20973158289266672499947279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13982105526177781666631519 20973158289266672499947279)
    ·
      refine ⟨31459737433900008749920919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20973158289266672499947279 31459737433900008749920919)
      ·
        refine ⟨47189606150850013124881379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31459737433900008749920919 47189606150850013124881379)
        ·
          refine ⟨70784409226275019687322069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47189606150850013124881379 70784409226275019687322069)
          ·
            refine ⟨1659009591240820773921611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70784409226275019687322069 1659009591240820773921611)
            ·
              refine ⟨2488514386861231160882417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659009591240820773921611 2488514386861231160882417)
              ·
                refine ⟨1866385790145923370661813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2488514386861231160882417 1866385790145923370661813)
                ·
                  refine ⟨174973667826180315999545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1866385790145923370661813 174973667826180315999545)
                  ·
                    rfl

theorem cell20_383355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_383355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383355 prefixEnd_383355 := by exact prefixLift 383355
  have htrace : WordTrace (prefixWord ++ tailWord_383355) baseStart_383355 baseEnd_383355 := by
    simpa [prefixWord, tailWord_383355, baseEnd_383355] using wordTrace_append hprefix tailTrace_383355
  have hstable : (prefixWord ++ tailWord_383355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383355).length < 2 ^ (prefixWord ++ tailWord_383355).sum := by decide
  have hdescent : baseEnd_383355 < baseStart_383355 := by decide
  rcases family_descends (prefixWord ++ tailWord_383355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383386 : List Nat := [3, 1, 1, 4, 1, 2, 1, 7]
def baseStart_383386 : Nat := 118140960795 + 383386 * 2 ^ 59
def prefixEnd_383386 : Nat := 4983230072969 + 3 ^ 40 * 383386 * 2
def baseEnd_383386 : Nat := 58329272356960661988695

theorem tailTrace_383386 : CollatzResearch.WordTrace tailWord_383386 prefixEnd_383386 58329272356960661988695 := by
  unfold tailWord_383386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495809047266368490252503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9322157459376982640673341 3495809047266368490252503)
  ·
    refine ⟨5243713570899552735378755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3495809047266368490252503 5243713570899552735378755)
    ·
      refine ⟨7865570356349329103068133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5243713570899552735378755 7865570356349329103068133)
      ·
        refine ⟨1474794441815499206825275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7865570356349329103068133 1474794441815499206825275)
        ·
          refine ⟨2212191662723248810237913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474794441815499206825275 2212191662723248810237913)
          ·
            refine ⟨1659143747042436607678435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2212191662723248810237913 1659143747042436607678435)
            ·
              refine ⟨2488715620563654911517653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659143747042436607678435 2488715620563654911517653)
              ·
                refine ⟨58329272356960661988695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2488715620563654911517653 58329272356960661988695)
                ·
                  rfl

theorem cell20_383386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_383386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383386 prefixEnd_383386 := by exact prefixLift 383386
  have htrace : WordTrace (prefixWord ++ tailWord_383386) baseStart_383386 baseEnd_383386 := by
    simpa [prefixWord, tailWord_383386, baseEnd_383386] using wordTrace_append hprefix tailTrace_383386
  have hstable : (prefixWord ++ tailWord_383386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383386).length < 2 ^ (prefixWord ++ tailWord_383386).sum := by decide
  have hdescent : baseEnd_383386 < baseStart_383386 := by decide
  rcases family_descends (prefixWord ++ tailWord_383386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383389 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 3]
def baseStart_383389 : Nat := 118140960795 + 383389 * 2 ^ 59
def prefixEnd_383389 : Nat := 4983230072969 + 3 ^ 40 * 383389 * 2
def baseEnd_383389 : Nat := 174989186352627308866073

theorem tailTrace_383389 : CollatzResearch.WordTrace tailWord_383389 prefixEnd_383389 174989186352627308866073 := by
  unfold tailWord_383389
  simp only [CollatzResearch.WordTrace]
  refine ⟨13983345608054605473369221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9322230405369736982246147 13983345608054605473369221)
  ·
    refine ⟨2621877301510238526256729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13983345608054605473369221 2621877301510238526256729)
    ·
      refine ⟨1966407976132678894692547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2621877301510238526256729 1966407976132678894692547)
      ·
        refine ⟨2949611964199018342038821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1966407976132678894692547 2949611964199018342038821)
        ·
          refine ⟨553052243287315939132279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2949611964199018342038821 553052243287315939132279)
          ·
            refine ⟨829578364930973908698419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553052243287315939132279 829578364930973908698419)
            ·
              refine ⟨1244367547396460863047629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829578364930973908698419 1244367547396460863047629)
              ·
                refine ⟨466637830273672823642861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1244367547396460863047629 466637830273672823642861)
                ·
                  refine ⟨174989186352627308866073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466637830273672823642861 174989186352627308866073)
                  ·
                    rfl

theorem cell20_383389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_383389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383389 prefixEnd_383389 := by exact prefixLift 383389
  have htrace : WordTrace (prefixWord ++ tailWord_383389) baseStart_383389 baseEnd_383389 := by
    simpa [prefixWord, tailWord_383389, baseEnd_383389] using wordTrace_append hprefix tailTrace_383389
  have hstable : (prefixWord ++ tailWord_383389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383389).length < 2 ^ (prefixWord ++ tailWord_383389).sum := by decide
  have hdescent : baseEnd_383389 < baseStart_383389 := by decide
  rcases family_descends (prefixWord ++ tailWord_383389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383434 : List Nat := [3, 1, 2, 1, 2, 2, 3, 4, 2]
def baseStart_383434 : Nat := 118140960795 + 383434 * 2 ^ 59
def prefixEnd_383434 : Nat := 4983230072969 + 3 ^ 40 * 383434 * 2
def baseEnd_383434 : Nat := 175009725578807152365889

theorem tailTrace_383434 : CollatzResearch.WordTrace tailWord_383434 prefixEnd_383434 175009725578807152365889 := by
  unfold tailWord_383434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3496246723222894539689339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9323324595261052105838237 3496246723222894539689339)
  ·
    refine ⟨5244370084834341809534009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3496246723222894539689339 5244370084834341809534009)
    ·
      refine ⟨3933277563625756357150507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5244370084834341809534009 3933277563625756357150507)
      ·
        refine ⟨5899916345438634535725761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933277563625756357150507 5899916345438634535725761)
        ·
          refine ⟨4424937259078975901794321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5899916345438634535725761 4424937259078975901794321)
          ·
            refine ⟨3318702944309231926345741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4424937259078975901794321 3318702944309231926345741)
            ·
              refine ⟨1244513604115961972379653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3318702944309231926345741 1244513604115961972379653)
              ·
                refine ⟨233346300771742869821185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1244513604115961972379653 233346300771742869821185)
                ·
                  refine ⟨175009725578807152365889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233346300771742869821185 175009725578807152365889)
                  ·
                    rfl

theorem cell20_383434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_383434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383434 prefixEnd_383434 := by exact prefixLift 383434
  have htrace : WordTrace (prefixWord ++ tailWord_383434) baseStart_383434 baseEnd_383434 := by
    simpa [prefixWord, tailWord_383434, baseEnd_383434] using wordTrace_append hprefix tailTrace_383434
  have hstable : (prefixWord ++ tailWord_383434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383434).length < 2 ^ (prefixWord ++ tailWord_383434).sum := by decide
  have hdescent : baseEnd_383434 < baseStart_383434 := by decide
  rcases family_descends (prefixWord ++ tailWord_383434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383455 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 4]
def baseStart_383455 : Nat := 118140960795 + 383455 * 2 ^ 59
def prefixEnd_383455 : Nat := 4983230072969 + 3 ^ 40 * 383455 * 2
def baseEnd_383455 : Nat := 175019310551024412665803

theorem tailTrace_383455 : CollatzResearch.WordTrace tailWord_383455 prefixEnd_383455 175019310551024412665803 := by
  unfold tailWord_383455
  simp only [CollatzResearch.WordTrace]
  refine ⟨13985752825815498745271819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9323835217210332496847879 13985752825815498745271819)
  ·
    refine ⟨20978629238723248117907729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13985752825815498745271819 20978629238723248117907729)
    ·
      refine ⟨15733971929042436088430797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20978629238723248117907729 15733971929042436088430797)
      ·
        refine ⟨5900239473390913533161549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15733971929042436088430797 5900239473390913533161549)
        ·
          refine ⟨2212589802521592574935581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5900239473390913533161549 2212589802521592574935581)
          ·
            refine ⟨829721175945597215600843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2212589802521592574935581 829721175945597215600843)
            ·
              refine ⟨1244581763918395823401265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829721175945597215600843 1244581763918395823401265)
              ·
                refine ⟨933436322938796867550949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244581763918395823401265 933436322938796867550949)
                ·
                  refine ⟨175019310551024412665803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933436322938796867550949 175019310551024412665803)
                  ·
                    rfl

theorem cell20_383455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_383455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383455 prefixEnd_383455 := by exact prefixLift 383455
  have htrace : WordTrace (prefixWord ++ tailWord_383455) baseStart_383455 baseEnd_383455 := by
    simpa [prefixWord, tailWord_383455, baseEnd_383455] using wordTrace_append hprefix tailTrace_383455
  have hstable : (prefixWord ++ tailWord_383455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383455).length < 2 ^ (prefixWord ++ tailWord_383455).sum := by decide
  have hdescent : baseEnd_383455 < baseStart_383455 := by decide
  rcases family_descends (prefixWord ++ tailWord_383455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383472 : List Nat := [2, 1, 1, 1, 3, 3, 4, 3, 2]
def baseStart_383472 : Nat := 118140960795 + 383472 * 2 ^ 59
def prefixEnd_383472 : Nat := 4983230072969 + 3 ^ 40 * 383472 * 2
def baseEnd_383472 : Nat := 175027069814247909099067

theorem tailTrace_383472 : CollatzResearch.WordTrace tailWord_383472 prefixEnd_383472 175027069814247909099067 := by
  unfold tailWord_383472
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993186433376955324320335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9324248577835940432427113 6993186433376955324320335)
  ·
    refine ⟨10489779650065432986480503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6993186433376955324320335 10489779650065432986480503)
    ·
      refine ⟨15734669475098149479720755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10489779650065432986480503 15734669475098149479720755)
      ·
        refine ⟨23602004212647224219581133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15734669475098149479720755 23602004212647224219581133)
        ·
          refine ⟨8850751579742709082342925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23602004212647224219581133 8850751579742709082342925)
          ·
            refine ⟨3319031842403515905878597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8850751579742709082342925 3319031842403515905878597)
            ·
              refine ⟨622318470450659232352237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3319031842403515905878597 622318470450659232352237)
              ·
                refine ⟨233369426418997212132089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622318470450659232352237 233369426418997212132089)
                ·
                  refine ⟨175027069814247909099067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233369426418997212132089 175027069814247909099067)
                  ·
                    rfl

theorem cell20_383472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_383472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383472 prefixEnd_383472 := by exact prefixLift 383472
  have htrace : WordTrace (prefixWord ++ tailWord_383472) baseStart_383472 baseEnd_383472 := by
    simpa [prefixWord, tailWord_383472, baseEnd_383472] using wordTrace_append hprefix tailTrace_383472
  have hstable : (prefixWord ++ tailWord_383472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383472).length < 2 ^ (prefixWord ++ tailWord_383472).sum := by decide
  have hdescent : baseEnd_383472 < baseStart_383472 := by decide
  rcases family_descends (prefixWord ++ tailWord_383472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383517 : List Nat := [1, 4, 2, 2, 1, 2, 4, 4]
def baseStart_383517 : Nat := 118140960795 + 383517 * 2 ^ 59
def prefixEnd_383517 : Nat := 4983230072969 + 3 ^ 40 * 383517 * 2
def baseEnd_383517 : Nat := 58349203013475917532961

theorem tailTrace_383517 : CollatzResearch.WordTrace tailWord_383517 prefixEnd_383517 58349203013475917532961 := by
  unfold tailWord_383517
  simp only [CollatzResearch.WordTrace]
  refine ⟨13988014151590883334028805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9325342767727255556019203 13988014151590883334028805)
  ·
    refine ⟨2622752653423290625130401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13988014151590883334028805 2622752653423290625130401)
    ·
      refine ⟨1967064490067467968847801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2622752653423290625130401 1967064490067467968847801)
      ·
        refine ⟨1475298367550600976635851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1967064490067467968847801 1475298367550600976635851)
        ·
          refine ⟨2212947551325901464953777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475298367550600976635851 2212947551325901464953777)
          ·
            refine ⟨1659710663494426098715333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2212947551325901464953777 1659710663494426098715333)
            ·
              refine ⟨311195749405204893509125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1659710663494426098715333 311195749405204893509125)
              ·
                refine ⟨58349203013475917532961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 311195749405204893509125 58349203013475917532961)
                ·
                  rfl

theorem cell20_383517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 4].length) (baseStart_383517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383517 prefixEnd_383517 := by exact prefixLift 383517
  have htrace : WordTrace (prefixWord ++ tailWord_383517) baseStart_383517 baseEnd_383517 := by
    simpa [prefixWord, tailWord_383517, baseEnd_383517] using wordTrace_append hprefix tailTrace_383517
  have hstable : (prefixWord ++ tailWord_383517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383517).length < 2 ^ (prefixWord ++ tailWord_383517).sum := by decide
  have hdescent : baseEnd_383517 < baseStart_383517 := by decide
  rcases family_descends (prefixWord ++ tailWord_383517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383534 : List Nat := [4, 1, 3, 1, 4, 1, 6]
def baseStart_383534 : Nat := 118140960795 + 383534 * 2 ^ 59
def prefixEnd_383534 : Nat := 4983230072969 + 3 ^ 40 * 383534 * 2
def baseEnd_383534 : Nat := 19450596478183472114683

theorem tailTrace_383534 : CollatzResearch.WordTrace tailWord_383534 prefixEnd_383534 19450596478183472114683 := by
  unfold tailWord_383534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1748579274066161904674707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9325756128352863491598437 1748579274066161904674707)
  ·
    refine ⟨2622868911099242857012061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1748579274066161904674707 2622868911099242857012061)
    ·
      refine ⟨983575841662216071379523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2622868911099242857012061 983575841662216071379523)
      ·
        refine ⟨1475363762493324107069285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983575841662216071379523 1475363762493324107069285)
        ·
          refine ⟨276630705467498270075491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1475363762493324107069285 276630705467498270075491)
          ·
            refine ⟨414946058201247405113237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276630705467498270075491 414946058201247405113237)
            ·
              refine ⟨19450596478183472114683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 414946058201247405113237 19450596478183472114683)
              ·
                rfl

theorem cell20_383534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 6].length) (baseStart_383534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383534 prefixEnd_383534 := by exact prefixLift 383534
  have htrace : WordTrace (prefixWord ++ tailWord_383534) baseStart_383534 baseEnd_383534 := by
    simpa [prefixWord, tailWord_383534, baseEnd_383534] using wordTrace_append hprefix tailTrace_383534
  have hstable : (prefixWord ++ tailWord_383534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383534).length < 2 ^ (prefixWord ++ tailWord_383534).sum := by decide
  have hdescent : baseEnd_383534 < baseStart_383534 := by decide
  rcases family_descends (prefixWord ++ tailWord_383534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383545 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_383545 : Nat := 118140960795 + 383545 * 2 ^ 59
def prefixEnd_383545 : Nat := 4983230072969 + 3 ^ 40 * 383545 * 2
def baseEnd_383545 : Nat := 175060389003384099665435

theorem tailTrace_383545 : CollatzResearch.WordTrace tailWord_383545 prefixEnd_383545 175060389003384099665435 := by
  unfold tailWord_383545
  simp only [CollatzResearch.WordTrace]
  refine ⟨13989035395489444116048089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9326023596992962744032059 13989035395489444116048089)
  ·
    refine ⟨10491776546617083087036067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13989035395489444116048089 10491776546617083087036067)
    ·
      refine ⟨15737664819925624630554101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10491776546617083087036067 15737664819925624630554101)
      ·
        refine ⟨1475406076868027309114447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15737664819925624630554101 1475406076868027309114447)
        ·
          refine ⟨2213109115302040963671671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475406076868027309114447 2213109115302040963671671)
          ·
            refine ⟨3319663672953061445507507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213109115302040963671671 3319663672953061445507507)
            ·
              refine ⟨4979495509429592168261261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3319663672953061445507507 4979495509429592168261261)
              ·
                refine ⟨1867310816036097063097973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4979495509429592168261261 1867310816036097063097973)
                ·
                  refine ⟨175060389003384099665435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1867310816036097063097973 175060389003384099665435)
                  ·
                    rfl

theorem cell20_383545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_383545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383545 prefixEnd_383545 := by exact prefixLift 383545
  have htrace : WordTrace (prefixWord ++ tailWord_383545) baseStart_383545 baseEnd_383545 := by
    simpa [prefixWord, tailWord_383545, baseEnd_383545] using wordTrace_append hprefix tailTrace_383545
  have hstable : (prefixWord ++ tailWord_383545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383545).length < 2 ^ (prefixWord ++ tailWord_383545).sum := by decide
  have hdescent : baseEnd_383545 < baseStart_383545 := by decide
  rcases family_descends (prefixWord ++ tailWord_383545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383548 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 4]
def baseStart_383548 : Nat := 118140960795 + 383548 * 2 ^ 59
def prefixEnd_383548 : Nat := 4983230072969 + 3 ^ 40 * 383548 * 2
def baseEnd_383548 : Nat := 175061758285129422565423

theorem tailTrace_383548 : CollatzResearch.WordTrace tailWord_383548 prefixEnd_383548 175061758285129422565423 := by
  unfold tailWord_383548
  simp only [CollatzResearch.WordTrace]
  refine ⟨6994572407239287814203649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9326096542985717085604865 6994572407239287814203649)
  ·
    refine ⟨5245929305429465860652737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6994572407239287814203649 5245929305429465860652737)
    ·
      refine ⟨3934446979072099395489553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5245929305429465860652737 3934446979072099395489553)
      ·
        refine ⟨2950835234304074546617165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3934446979072099395489553 2950835234304074546617165)
        ·
          refine ⟨1106563212864027954981437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2950835234304074546617165 1106563212864027954981437)
          ·
            refine ⟨414961204824010483118039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1106563212864027954981437 414961204824010483118039)
            ·
              refine ⟨622441807236015724677059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414961204824010483118039 622441807236015724677059)
              ·
                refine ⟨933662710854023587015589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622441807236015724677059 933662710854023587015589)
                ·
                  refine ⟨175061758285129422565423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933662710854023587015589 175061758285129422565423)
                  ·
                    rfl

theorem cell20_383548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_383548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383548 prefixEnd_383548 := by exact prefixLift 383548
  have htrace : WordTrace (prefixWord ++ tailWord_383548) baseStart_383548 baseEnd_383548 := by
    simpa [prefixWord, tailWord_383548, baseEnd_383548] using wordTrace_append hprefix tailTrace_383548
  have hstable : (prefixWord ++ tailWord_383548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383548).length < 2 ^ (prefixWord ++ tailWord_383548).sum := by decide
  have hdescent : baseEnd_383548 < baseStart_383548 := by decide
  rcases family_descends (prefixWord ++ tailWord_383548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383558 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_383558 : Nat := 118140960795 + 383558 * 2 ^ 59
def prefixEnd_383558 : Nat := 4983230072969 + 3 ^ 40 * 383558 * 2
def baseEnd_383558 : Nat := 175066322557613832232049

theorem tailTrace_383558 : CollatzResearch.WordTrace tailWord_383558 prefixEnd_383558 175066322557613832232049 := by
  unfold tailWord_383558
  simp only [CollatzResearch.WordTrace]
  refine ⟨437172173263823354258479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9326339696294898224180885 437172173263823354258479)
  ·
    refine ⟨655758259895735031387719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437172173263823354258479 655758259895735031387719)
    ·
      refine ⟨983637389843602547081579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655758259895735031387719 983637389843602547081579)
      ·
        refine ⟨1475456084765403820622369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983637389843602547081579 1475456084765403820622369)
        ·
          refine ⟨1106592063574052865466777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1475456084765403820622369 1106592063574052865466777)
          ·
            refine ⟨829944047680539649100083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106592063574052865466777 829944047680539649100083)
            ·
              refine ⟨1244916071520809473650125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829944047680539649100083 1244916071520809473650125)
              ·
                refine ⟨466843526820303552618797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1244916071520809473650125 466843526820303552618797)
                ·
                  refine ⟨175066322557613832232049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466843526820303552618797 175066322557613832232049)
                  ·
                    rfl

theorem cell20_383558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_383558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383558 prefixEnd_383558 := by exact prefixLift 383558
  have htrace : WordTrace (prefixWord ++ tailWord_383558) baseStart_383558 baseEnd_383558 := by
    simpa [prefixWord, tailWord_383558, baseEnd_383558] using wordTrace_append hprefix tailTrace_383558
  have hstable : (prefixWord ++ tailWord_383558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383558).length < 2 ^ (prefixWord ++ tailWord_383558).sum := by decide
  have hdescent : baseEnd_383558 < baseStart_383558 := by decide
  rcases family_descends (prefixWord ++ tailWord_383558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383562 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_383562 : Nat := 118140960795 + 383562 * 2 ^ 59
def prefixEnd_383562 : Nat := 4983230072969 + 3 ^ 40 * 383562 * 2
def baseEnd_383562 : Nat := 175068148266607596098699

theorem tailTrace_383562 : CollatzResearch.WordTrace tailWord_383562 prefixEnd_383562 175068148266607596098699 := by
  unfold tailWord_383562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3497413859106964004854235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9326436957618570679611293 3497413859106964004854235)
  ·
    refine ⟨5246120788660446007281353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3497413859106964004854235 5246120788660446007281353)
    ·
      refine ⟨3934590591495334505461015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5246120788660446007281353 3934590591495334505461015)
      ·
        refine ⟨5901885887243001758191523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3934590591495334505461015 5901885887243001758191523)
        ·
          refine ⟨8852828830864502637287285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5901885887243001758191523 8852828830864502637287285)
          ·
            refine ⟨829952702893547122245683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8852828830864502637287285 829952702893547122245683)
            ·
              refine ⟨1244929054340320683368525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829952702893547122245683 1244929054340320683368525)
              ·
                refine ⟨466848395377620256263197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1244929054340320683368525 466848395377620256263197)
                ·
                  refine ⟨175068148266607596098699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466848395377620256263197 175068148266607596098699)
                  ·
                    rfl

theorem cell20_383562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_383562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383562 prefixEnd_383562 := by exact prefixLift 383562
  have htrace : WordTrace (prefixWord ++ tailWord_383562) baseStart_383562 baseEnd_383562 := by
    simpa [prefixWord, tailWord_383562, baseEnd_383562] using wordTrace_append hprefix tailTrace_383562
  have hstable : (prefixWord ++ tailWord_383562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383562).length < 2 ^ (prefixWord ++ tailWord_383562).sum := by decide
  have hdescent : baseEnd_383562 < baseStart_383562 := by decide
  rcases family_descends (prefixWord ++ tailWord_383562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383655 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 5]
def baseStart_383655 : Nat := 118140960795 + 383655 * 2 ^ 59
def prefixEnd_383655 : Nat := 4983230072969 + 3 ^ 40 * 383655 * 2
def baseEnd_383655 : Nat := 175110596000712605998319

theorem tailTrace_383655 : CollatzResearch.WordTrace tailWord_383655 prefixEnd_383655 175110596000712605998319 := by
  unfold tailWord_383655
  simp only [CollatzResearch.WordTrace]
  refine ⟨13993047425090932902552419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9328698283393955268368279 13993047425090932902552419)
  ·
    refine ⟨20989571137636399353828629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13993047425090932902552419 20989571137636399353828629)
    ·
      refine ⟨983886147076706219710717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20989571137636399353828629 983886147076706219710717)
      ·
        refine ⟨368957305153764832391519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 983886147076706219710717 368957305153764832391519)
        ·
          refine ⟨553435957730647248587279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368957305153764832391519 553435957730647248587279)
          ·
            refine ⟨830153936595970872880919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553435957730647248587279 830153936595970872880919)
            ·
              refine ⟨1245230904893956309321379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830153936595970872880919 1245230904893956309321379)
              ·
                refine ⟨1867846357340934463982069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245230904893956309321379 1867846357340934463982069)
                ·
                  refine ⟨175110596000712605998319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1867846357340934463982069 175110596000712605998319)
                  ·
                    rfl

theorem cell20_383655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 5].length) (baseStart_383655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383655 prefixEnd_383655 := by exact prefixLift 383655
  have htrace : WordTrace (prefixWord ++ tailWord_383655) baseStart_383655 baseEnd_383655 := by
    simpa [prefixWord, tailWord_383655, baseEnd_383655] using wordTrace_append hprefix tailTrace_383655
  have hstable : (prefixWord ++ tailWord_383655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383655).length < 2 ^ (prefixWord ++ tailWord_383655).sum := by decide
  have hdescent : baseEnd_383655 < baseStart_383655 := by decide
  rcases family_descends (prefixWord ++ tailWord_383655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383662 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_383662 : Nat := 118140960795 + 383662 * 2 ^ 59
def prefixEnd_383662 : Nat := 4983230072969 + 3 ^ 40 * 383662 * 2
def baseEnd_383662 : Nat := 175113790991451692764957

theorem tailTrace_383662 : CollatzResearch.WordTrace tailWord_383662 prefixEnd_383662 175113790991451692764957 := by
  unfold tailWord_383662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1749162842008196637257155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9328868490710382065371493 1749162842008196637257155)
  ·
    refine ⟨2623744263012294955885733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1749162842008196637257155 2623744263012294955885733)
    ·
      refine ⟨491952049314805304228575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2623744263012294955885733 491952049314805304228575)
      ·
        refine ⟨737928073972207956342863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491952049314805304228575 737928073972207956342863)
        ·
          refine ⟨1106892110958311934514295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737928073972207956342863 1106892110958311934514295)
          ·
            refine ⟨1660338166437467901771443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106892110958311934514295 1660338166437467901771443)
            ·
              refine ⟨2490507249656201852657165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660338166437467901771443 2490507249656201852657165)
              ·
                refine ⟨933940218621075694746437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2490507249656201852657165 933940218621075694746437)
                ·
                  refine ⟨175113790991451692764957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933940218621075694746437 175113790991451692764957)
                  ·
                    rfl

theorem cell20_383662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_383662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383662 prefixEnd_383662 := by exact prefixLift 383662
  have htrace : WordTrace (prefixWord ++ tailWord_383662) baseStart_383662 baseEnd_383662 := by
    simpa [prefixWord, tailWord_383662, baseEnd_383662] using wordTrace_append hprefix tailTrace_383662
  have hstable : (prefixWord ++ tailWord_383662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383662).length < 2 ^ (prefixWord ++ tailWord_383662).sum := by decide
  have hdescent : baseEnd_383662 < baseStart_383662 := by decide
  rcases family_descends (prefixWord ++ tailWord_383662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383673 : List Nat := [1, 2, 1, 4, 1, 1, 1, 9]
def baseStart_383673 : Nat := 118140960795 + 383673 * 2 ^ 59
def prefixEnd_383673 : Nat := 4983230072969 + 3 ^ 40 * 383673 * 2
def baseEnd_383673 : Nat := 58372937230394847799415

theorem tailTrace_383673 : CollatzResearch.WordTrace tailWord_383673 prefixEnd_383673 58372937230394847799415 := by
  unfold tailWord_383673
  simp only [CollatzResearch.WordTrace]
  refine ⟨13993703939025721976707673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9329135959350481317805115 13993703939025721976707673)
  ·
    refine ⟨10495277954269291482530755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13993703939025721976707673 10495277954269291482530755)
    ·
      refine ⟨15742916931403937223796133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10495277954269291482530755 15742916931403937223796133)
      ·
        refine ⟨2951796924638238229461775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15742916931403937223796133 2951796924638238229461775)
        ·
          refine ⟨4427695386957357344192663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951796924638238229461775 4427695386957357344192663)
          ·
            refine ⟨6641543080436036016288995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427695386957357344192663 6641543080436036016288995)
            ·
              refine ⟨9962314620654054024433493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641543080436036016288995 9962314620654054024433493)
              ·
                refine ⟨58372937230394847799415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9962314620654054024433493 58372937230394847799415)
                ·
                  rfl

theorem cell20_383673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_383673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383673 prefixEnd_383673 := by exact prefixLift 383673
  have htrace : WordTrace (prefixWord ++ tailWord_383673) baseStart_383673 baseEnd_383673 := by
    simpa [prefixWord, tailWord_383673, baseEnd_383673] using wordTrace_append hprefix tailTrace_383673
  have hstable : (prefixWord ++ tailWord_383673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383673).length < 2 ^ (prefixWord ++ tailWord_383673).sum := by decide
  have hdescent : baseEnd_383673 < baseStart_383673 := by decide
  rcases family_descends (prefixWord ++ tailWord_383673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383690 : List Nat := [3, 1, 2, 1, 4, 2, 1, 6]
def baseStart_383690 : Nat := 118140960795 + 383690 * 2 ^ 59
def prefixEnd_383690 : Nat := 4983230072969 + 3 ^ 40 * 383690 * 2
def baseEnd_383690 : Nat := 58375523651469346610503

theorem tailTrace_383690 : CollatzResearch.WordTrace tailWord_383690 prefixEnd_383690 58375523651469346610503 := by
  unfold tailWord_383690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3498580994991033470019131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9329549319976089253384349 3498580994991033470019131)
  ·
    refine ⟨5247871492486550205028697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3498580994991033470019131 5247871492486550205028697)
    ·
      refine ⟨3935903619364912653771523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5247871492486550205028697 3935903619364912653771523)
      ·
        refine ⟨5903855429047368980657285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3935903619364912653771523 5903855429047368980657285)
        ·
          refine ⟨1106972892946381683873241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5903855429047368980657285 1106972892946381683873241)
          ·
            refine ⟨830229669709786262904931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106972892946381683873241 830229669709786262904931)
            ·
              refine ⟨1245344504564679394357397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830229669709786262904931 1245344504564679394357397)
              ·
                refine ⟨58375523651469346610503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1245344504564679394357397 58375523651469346610503)
                ·
                  rfl

theorem cell20_383690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_383690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383690 prefixEnd_383690 := by exact prefixLift 383690
  have htrace : WordTrace (prefixWord ++ tailWord_383690) baseStart_383690 baseEnd_383690 := by
    simpa [prefixWord, tailWord_383690, baseEnd_383690] using wordTrace_append hprefix tailTrace_383690
  have hstable : (prefixWord ++ tailWord_383690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383690).length < 2 ^ (prefixWord ++ tailWord_383690).sum := by decide
  have hdescent : baseEnd_383690 < baseStart_383690 := by decide
  rcases family_descends (prefixWord ++ tailWord_383690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383711 : List Nat := [1, 1, 2, 3, 2, 3, 8]
def baseStart_383711 : Nat := 118140960795 + 383711 * 2 ^ 59
def prefixEnd_383711 : Nat := 4983230072969 + 3 ^ 40 * 383711 * 2
def baseEnd_383711 : Nat := 19459572880736144459047

theorem tailTrace_383711 : CollatzResearch.WordTrace tailWord_383711 prefixEnd_383711 19459572880736144459047 := by
  unfold tailWord_383711
  simp only [CollatzResearch.WordTrace]
  refine ⟨13995089912888054466590987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9330059941925369644393991 13995089912888054466590987)
  ·
    refine ⟨20992634869332081699886481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13995089912888054466590987 20992634869332081699886481)
    ·
      refine ⟨15744476151999061274914861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20992634869332081699886481 15744476151999061274914861)
      ·
        refine ⟨5904178556999647978093073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15744476151999061274914861 5904178556999647978093073)
        ·
          refine ⟨4428133917749735983569805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5904178556999647978093073 4428133917749735983569805)
          ·
            refine ⟨1660550219156150993838677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4428133917749735983569805 1660550219156150993838677)
            ·
              refine ⟨19459572880736144459047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1660550219156150993838677 19459572880736144459047)
              ·
                rfl

theorem cell20_383711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 8].length) (baseStart_383711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383711 prefixEnd_383711 := by exact prefixLift 383711
  have htrace : WordTrace (prefixWord ++ tailWord_383711) baseStart_383711 baseEnd_383711 := by
    simpa [prefixWord, tailWord_383711, baseEnd_383711] using wordTrace_append hprefix tailTrace_383711
  have hstable : (prefixWord ++ tailWord_383711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383711).length < 2 ^ (prefixWord ++ tailWord_383711).sum := by decide
  have hdescent : baseEnd_383711 < baseStart_383711 := by decide
  rcases family_descends (prefixWord ++ tailWord_383711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383717 : List Nat := [1, 3, 1, 4, 1, 3, 3, 2, 2]
def baseStart_383717 : Nat := 118140960795 + 383717 * 2 ^ 59
def prefixEnd_383717 : Nat := 4983230072969 + 3 ^ 40 * 383717 * 2
def baseEnd_383717 : Nat := 175138894490115945931399

theorem tailTrace_383717 : CollatzResearch.WordTrace tailWord_383717 prefixEnd_383717 175138894490115945931399 := by
  unfold tailWord_383717
  simp only [CollatzResearch.WordTrace]
  refine ⟨13995308750866317491309405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9330205833910878327539603 13995308750866317491309405)
  ·
    refine ⟨5248240781574869059241027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13995308750866317491309405 5248240781574869059241027)
    ·
      refine ⟨7872361172362303588861541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5248240781574869059241027 7872361172362303588861541)
      ·
        refine ⟨1476067719817931922911539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7872361172362303588861541 1476067719817931922911539)
        ·
          refine ⟨2214101579726897884367309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476067719817931922911539 2214101579726897884367309)
          ·
            refine ⟨830288092397586706637741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2214101579726897884367309 830288092397586706637741)
            ·
              refine ⟨311358034649095014989153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 830288092397586706637741 311358034649095014989153)
              ·
                refine ⟨233518525986821261241865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311358034649095014989153 233518525986821261241865)
                ·
                  refine ⟨175138894490115945931399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233518525986821261241865 175138894490115945931399)
                  ·
                    rfl

theorem cell20_383717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_383717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383717 prefixEnd_383717 := by exact prefixLift 383717
  have htrace : WordTrace (prefixWord ++ tailWord_383717) baseStart_383717 baseEnd_383717 := by
    simpa [prefixWord, tailWord_383717, baseEnd_383717] using wordTrace_append hprefix tailTrace_383717
  have hstable : (prefixWord ++ tailWord_383717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383717).length < 2 ^ (prefixWord ++ tailWord_383717).sum := by decide
  have hdescent : baseEnd_383717 < baseStart_383717 := by decide
  rcases family_descends (prefixWord ++ tailWord_383717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383721 : List Nat := [1, 2, 1, 1, 1, 2, 4, 6, 2]
def baseStart_383721 : Nat := 118140960795 + 383721 * 2 ^ 59
def prefixEnd_383721 : Nat := 4983230072969 + 3 ^ 40 * 383721 * 2
def baseEnd_383721 : Nat := 175140720199109709798049

theorem tailTrace_383721 : CollatzResearch.WordTrace tailWord_383721 prefixEnd_383721 175140720199109709798049 := by
  unfold tailWord_383721
  simp only [CollatzResearch.WordTrace]
  refine ⟨13995454642851826174455017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9330303095234550782970011 13995454642851826174455017)
  ·
    refine ⟨10496590982138869630841263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13995454642851826174455017 10496590982138869630841263)
    ·
      refine ⟨15744886473208304446261895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10496590982138869630841263 15744886473208304446261895)
      ·
        refine ⟨23617329709812456669392843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15744886473208304446261895 23617329709812456669392843)
        ·
          refine ⟨35425994564718685004089265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23617329709812456669392843 35425994564718685004089265)
          ·
            refine ⟨26569495923539013753066949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35425994564718685004089265 26569495923539013753066949)
            ·
              refine ⟨4981780485663565078700053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26569495923539013753066949 4981780485663565078700053)
              ·
                refine ⟨233520960265479613064065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4981780485663565078700053 233520960265479613064065)
                ·
                  refine ⟨175140720199109709798049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233520960265479613064065 175140720199109709798049)
                  ·
                    rfl

theorem cell20_383721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_383721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383721 prefixEnd_383721 := by exact prefixLift 383721
  have htrace : WordTrace (prefixWord ++ tailWord_383721) baseStart_383721 baseEnd_383721 := by
    simpa [prefixWord, tailWord_383721, baseEnd_383721] using wordTrace_append hprefix tailTrace_383721
  have hstable : (prefixWord ++ tailWord_383721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383721).length < 2 ^ (prefixWord ++ tailWord_383721).sum := by decide
  have hdescent : baseEnd_383721 < baseStart_383721 := by decide
  rcases family_descends (prefixWord ++ tailWord_383721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383759 : List Nat := [1, 1, 2, 1, 1, 1, 6, 5, 2]
def baseStart_383759 : Nat := 118140960795 + 383759 * 2 ^ 59
def prefixEnd_383759 : Nat := 4983230072969 + 3 ^ 40 * 383759 * 2
def baseEnd_383759 : Nat := 175158064434550466531227

theorem tailTrace_383759 : CollatzResearch.WordTrace tailWord_383759 prefixEnd_383759 175158064434550466531227 := by
  unfold tailWord_383759
  simp only [CollatzResearch.WordTrace]
  refine ⟨13996840616714158664338331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9331227077809439109558887 13996840616714158664338331)
  ·
    refine ⟨20995260925071237996507497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13996840616714158664338331 20995260925071237996507497)
    ·
      refine ⟨15746445693803428497380623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20995260925071237996507497 15746445693803428497380623)
      ·
        refine ⟨23619668540705142746070935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15746445693803428497380623 23619668540705142746070935)
        ·
          refine ⟨35429502811057714119106403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23619668540705142746070935 35429502811057714119106403)
          ·
            refine ⟨53144254216586571178659605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35429502811057714119106403 53144254216586571178659605)
            ·
              refine ⟨2491136916402495523999669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53144254216586571178659605 2491136916402495523999669)
              ·
                refine ⟨233544085912733955374969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2491136916402495523999669 233544085912733955374969)
                ·
                  refine ⟨175158064434550466531227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233544085912733955374969 175158064434550466531227)
                  ·
                    rfl

theorem cell20_383759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 2].length) (baseStart_383759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383759 prefixEnd_383759 := by exact prefixLift 383759
  have htrace : WordTrace (prefixWord ++ tailWord_383759) baseStart_383759 baseEnd_383759 := by
    simpa [prefixWord, tailWord_383759, baseEnd_383759] using wordTrace_append hprefix tailTrace_383759
  have hstable : (prefixWord ++ tailWord_383759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383759).length < 2 ^ (prefixWord ++ tailWord_383759).sum := by decide
  have hdescent : baseEnd_383759 < baseStart_383759 := by decide
  rcases family_descends (prefixWord ++ tailWord_383759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383776 : List Nat := [2, 1, 1, 5, 1, 3, 1, 4, 2]
def baseStart_383776 : Nat := 118140960795 + 383776 * 2 ^ 59
def prefixEnd_383776 : Nat := 4983230072969 + 3 ^ 40 * 383776 * 2
def baseEnd_383776 : Nat := 175165823697773962964491

theorem tailTrace_383776 : CollatzResearch.WordTrace tailWord_383776 prefixEnd_383776 175165823697773962964491 := by
  unfold tailWord_383776
  simp only [CollatzResearch.WordTrace]
  refine ⟨6998730328826285283853591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9331640438435047045138121 6998730328826285283853591)
  ·
    refine ⟨10498095493239427925780387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6998730328826285283853591 10498095493239427925780387)
    ·
      refine ⟨15747143239859141888670581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10498095493239427925780387 15747143239859141888670581)
      ·
        refine ⟨1476294678736794552062867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15747143239859141888670581 1476294678736794552062867)
        ·
          refine ⟨2214442018105191828094301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476294678736794552062867 2214442018105191828094301)
          ·
            refine ⟨830415756789446935535363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2214442018105191828094301 830415756789446935535363)
            ·
              refine ⟨1245623635184170403303045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830415756789446935535363 1245623635184170403303045)
              ·
                refine ⟨233554431597031950619321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1245623635184170403303045 233554431597031950619321)
                ·
                  refine ⟨175165823697773962964491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233554431597031950619321 175165823697773962964491)
                  ·
                    rfl

theorem cell20_383776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_383776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383776 prefixEnd_383776 := by exact prefixLift 383776
  have htrace : WordTrace (prefixWord ++ tailWord_383776) baseStart_383776 baseEnd_383776 := by
    simpa [prefixWord, tailWord_383776, baseEnd_383776] using wordTrace_append hprefix tailTrace_383776
  have hstable : (prefixWord ++ tailWord_383776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383776).length < 2 ^ (prefixWord ++ tailWord_383776).sum := by decide
  have hdescent : baseEnd_383776 < baseStart_383776 := by decide
  rcases family_descends (prefixWord ++ tailWord_383776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383797 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 4]
def baseStart_383797 : Nat := 118140960795 + 383797 * 2 ^ 59
def prefixEnd_383797 : Nat := 4983230072969 + 3 ^ 40 * 383797 * 2
def baseEnd_383797 : Nat := 175175408669991223264405

theorem tailTrace_383797 : CollatzResearch.WordTrace tailWord_383797 prefixEnd_383797 175175408669991223264405 := by
  unfold tailWord_383797
  simp only [CollatzResearch.WordTrace]
  refine ⟨13998226590576491154221645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9332151060384327436147763 13998226590576491154221645)
  ·
    refine ⟨5249334971466184182833117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13998226590576491154221645 5249334971466184182833117)
    ·
      refine ⟨1968500614299819068562419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5249334971466184182833117 1968500614299819068562419)
      ·
        refine ⟨2952750921449728602843629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968500614299819068562419 2952750921449728602843629)
        ·
          refine ⟨1107281595543648226066361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2952750921449728602843629 1107281595543648226066361)
          ·
            refine ⟨830461196657736169549771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107281595543648226066361 830461196657736169549771)
            ·
              refine ⟨1245691794986604254324657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830461196657736169549771 1245691794986604254324657)
              ·
                refine ⟨934268846239953190743493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1245691794986604254324657 934268846239953190743493)
                ·
                  refine ⟨175175408669991223264405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 934268846239953190743493 175175408669991223264405)
                  ·
                    rfl

theorem cell20_383797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_383797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383797 prefixEnd_383797 := by exact prefixLift 383797
  have htrace : WordTrace (prefixWord ++ tailWord_383797) baseStart_383797 baseEnd_383797 := by
    simpa [prefixWord, tailWord_383797, baseEnd_383797] using wordTrace_append hprefix tailTrace_383797
  have hstable : (prefixWord ++ tailWord_383797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383797).length < 2 ^ (prefixWord ++ tailWord_383797).sum := by decide
  have hdescent : baseEnd_383797 < baseStart_383797 := by decide
  rcases family_descends (prefixWord ++ tailWord_383797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383821 : List Nat := [1, 6, 1, 2, 2, 1, 7]
def baseStart_383821 : Nat := 118140960795 + 383821 * 2 ^ 59
def prefixEnd_383821 : Nat := 4983230072969 + 3 ^ 40 * 383821 * 2
def baseEnd_383821 : Nat := 19465151435994867384923

theorem tailTrace_383821 : CollatzResearch.WordTrace tailWord_383821 prefixEnd_383821 19465151435994867384923 := by
  unfold tailWord_383821
  simp only [CollatzResearch.WordTrace]
  refine ⟨13999101942489543253095317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9332734628326362168730211 13999101942489543253095317)
  ·
    refine ⟨656207903554197339988843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13999101942489543253095317 656207903554197339988843)
    ·
      refine ⟨984311855331296009983265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 656207903554197339988843 984311855331296009983265)
      ·
        refine ⟨738233891498472007487449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 984311855331296009983265 738233891498472007487449)
        ·
          refine ⟨553675418623854005615587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738233891498472007487449 553675418623854005615587)
          ·
            refine ⟨830513127935781008423381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553675418623854005615587 830513127935781008423381)
            ·
              refine ⟨19465151435994867384923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 830513127935781008423381 19465151435994867384923)
              ·
                rfl

theorem cell20_383821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 7].length) (baseStart_383821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383821 prefixEnd_383821 := by exact prefixLift 383821
  have htrace : WordTrace (prefixWord ++ tailWord_383821) baseStart_383821 baseEnd_383821 := by
    simpa [prefixWord, tailWord_383821, baseEnd_383821] using wordTrace_append hprefix tailTrace_383821
  have hstable : (prefixWord ++ tailWord_383821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383821).length < 2 ^ (prefixWord ++ tailWord_383821).sum := by decide
  have hdescent : baseEnd_383821 < baseStart_383821 := by decide
  rcases family_descends (prefixWord ++ tailWord_383821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383828 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 5]
def baseStart_383828 : Nat := 118140960795 + 383828 * 2 ^ 59
def prefixEnd_383828 : Nat := 4983230072969 + 3 ^ 40 * 383828 * 2
def baseEnd_383828 : Nat := 175189557914692893230945

theorem tailTrace_383828 : CollatzResearch.WordTrace tailWord_383828 prefixEnd_383828 175189557914692893230945 := by
  unfold tailWord_383828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6999678626732091724300069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9332904835642788965733425 6999678626732091724300069)
  ·
    refine ⟨1312439742512267198306263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6999678626732091724300069 1312439742512267198306263)
    ·
      refine ⟨1968659613768400797459395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1312439742512267198306263 1968659613768400797459395)
      ·
        refine ⟨2952989420652601196189093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968659613768400797459395 2952989420652601196189093)
        ·
          refine ⟨553685516372362724285455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2952989420652601196189093 553685516372362724285455)
          ·
            refine ⟨830528274558544086428183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553685516372362724285455 830528274558544086428183)
            ·
              refine ⟨1245792411837816129642275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830528274558544086428183 1245792411837816129642275)
              ·
                refine ⟨1868688617756724194463413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245792411837816129642275 1868688617756724194463413)
                ·
                  refine ⟨175189557914692893230945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1868688617756724194463413 175189557914692893230945)
                  ·
                    rfl

theorem cell20_383828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_383828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383828 prefixEnd_383828 := by exact prefixLift 383828
  have htrace : WordTrace (prefixWord ++ tailWord_383828) baseStart_383828 baseEnd_383828 := by
    simpa [prefixWord, tailWord_383828, baseEnd_383828] using wordTrace_append hprefix tailTrace_383828
  have hstable : (prefixWord ++ tailWord_383828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383828).length < 2 ^ (prefixWord ++ tailWord_383828).sum := by decide
  have hdescent : baseEnd_383828 < baseStart_383828 := by decide
  rcases family_descends (prefixWord ++ tailWord_383828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383856 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_383856 : Nat := 118140960795 + 383856 * 2 ^ 59
def prefixEnd_383856 : Nat := 4983230072969 + 3 ^ 40 * 383856 * 2
def baseEnd_383856 : Nat := 175202337877649240297497

theorem tailTrace_383856 : CollatzResearch.WordTrace tailWord_383856 prefixEnd_383856 175202337877649240297497 := by
  unfold tailWord_383856
  simp only [CollatzResearch.WordTrace]
  refine ⟨7000189248681372115309711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9333585664908496153746281 7000189248681372115309711)
  ·
    refine ⟨10500283873022058172964567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7000189248681372115309711 10500283873022058172964567)
    ·
      refine ⟨15750425809533087259446851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10500283873022058172964567 15750425809533087259446851)
      ·
        refine ⟨23625638714299630889170277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15750425809533087259446851 23625638714299630889170277)
        ·
          refine ⟨4429807258931180791719427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23625638714299630889170277 4429807258931180791719427)
          ·
            refine ⟨6644710888396771187579141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4429807258931180791719427 6644710888396771187579141)
            ·
              refine ⟨1245883291574394597671089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6644710888396771187579141 1245883291574394597671089)
              ·
                refine ⟨934412468680795948253317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1245883291574394597671089 934412468680795948253317)
                ·
                  refine ⟨175202337877649240297497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 934412468680795948253317 175202337877649240297497)
                  ·
                    rfl

theorem cell20_383856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_383856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383856 prefixEnd_383856 := by exact prefixLift 383856
  have htrace : WordTrace (prefixWord ++ tailWord_383856) baseStart_383856 baseEnd_383856 := by
    simpa [prefixWord, tailWord_383856, baseEnd_383856] using wordTrace_append hprefix tailTrace_383856
  have hstable : (prefixWord ++ tailWord_383856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383856).length < 2 ^ (prefixWord ++ tailWord_383856).sum := by decide
  have hdescent : baseEnd_383856 < baseStart_383856 := by decide
  rcases family_descends (prefixWord ++ tailWord_383856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383880 : List Nat := [2, 1, 3, 3, 2, 3, 6]
def baseStart_383880 : Nat := 118140960795 + 383880 * 2 ^ 59
def prefixEnd_383880 : Nat := 4983230072969 + 3 ^ 40 * 383880 * 2
def baseEnd_383880 : Nat := 19468143570179091499711

theorem tailTrace_383880 : CollatzResearch.WordTrace tailWord_383880 prefixEnd_383880 19468143570179091499711 := by
  unfold tailWord_383880
  simp only [CollatzResearch.WordTrace]
  refine ⟨7000626924637898164746547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9334169232850530886328729 7000626924637898164746547)
  ·
    refine ⟨10500940386956847247119821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7000626924637898164746547 10500940386956847247119821)
    ·
      refine ⟨3937852645108817717669933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10500940386956847247119821 3937852645108817717669933)
      ·
        refine ⟨1476694741915806644126225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3937852645108817717669933 1476694741915806644126225)
        ·
          refine ⟨1107521056436854983094669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1476694741915806644126225 1107521056436854983094669)
          ·
            refine ⟨415320396163820618660501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1107521056436854983094669 415320396163820618660501)
            ·
              refine ⟨19468143570179091499711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 415320396163820618660501 19468143570179091499711)
              ·
                rfl

theorem cell20_383880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 6].length) (baseStart_383880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383880 prefixEnd_383880 := by exact prefixLift 383880
  have htrace : WordTrace (prefixWord ++ tailWord_383880) baseStart_383880 baseEnd_383880 := by
    simpa [prefixWord, tailWord_383880, baseEnd_383880] using wordTrace_append hprefix tailTrace_383880
  have hstable : (prefixWord ++ tailWord_383880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383880).length < 2 ^ (prefixWord ++ tailWord_383880).sum := by decide
  have hdescent : baseEnd_383880 < baseStart_383880 := by decide
  rcases family_descends (prefixWord ++ tailWord_383880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383900 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 3]
def baseStart_383900 : Nat := 118140960795 + 383900 * 2 ^ 59
def prefixEnd_383900 : Nat := 4983230072969 + 3 ^ 40 * 383900 * 2
def baseEnd_383900 : Nat := 175222420676580642830651

theorem tailTrace_383900 : CollatzResearch.WordTrace tailWord_383900 prefixEnd_383900 175222420676580642830651 := by
  unfold tailWord_383900
  simp only [CollatzResearch.WordTrace]
  refine ⟨7000991654601669872610577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9334655539468893163480769 7000991654601669872610577)
  ·
    refine ⟨5250743740951252404457933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7000991654601669872610577 5250743740951252404457933)
    ·
      refine ⟨1969028902856719651671725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5250743740951252404457933 1969028902856719651671725)
      ·
        refine ⟨738385838571269869376897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1969028902856719651671725 738385838571269869376897)
        ·
          refine ⟨553789378928452402032673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738385838571269869376897 553789378928452402032673)
          ·
            refine ⟨415342034196339301524505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553789378928452402032673 415342034196339301524505)
            ·
              refine ⟨311506525647254476143379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415342034196339301524505 311506525647254476143379)
              ·
                refine ⟨467259788470881714215069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311506525647254476143379 467259788470881714215069)
                ·
                  refine ⟨175222420676580642830651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467259788470881714215069 175222420676580642830651)
                  ·
                    rfl

theorem cell20_383900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_383900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383900 prefixEnd_383900 := by exact prefixLift 383900
  have htrace : WordTrace (prefixWord ++ tailWord_383900) baseStart_383900 baseEnd_383900 := by
    simpa [prefixWord, tailWord_383900, baseEnd_383900] using wordTrace_append hprefix tailTrace_383900
  have hstable : (prefixWord ++ tailWord_383900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383900).length < 2 ^ (prefixWord ++ tailWord_383900).sum := by decide
  have hdescent : baseEnd_383900 < baseStart_383900 := by decide
  rcases family_descends (prefixWord ++ tailWord_383900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383904 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 3]
def baseStart_383904 : Nat := 118140960795 + 383904 * 2 ^ 59
def prefixEnd_383904 : Nat := 4983230072969 + 3 ^ 40 * 383904 * 2
def baseEnd_383904 : Nat := 175224246385574406697301

theorem tailTrace_383904 : CollatzResearch.WordTrace tailWord_383904 prefixEnd_383904 175224246385574406697301 := by
  unfold tailWord_383904
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001064600594424214183383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9334752800792565618911177 7001064600594424214183383)
  ·
    refine ⟨10501596900891636321275075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7001064600594424214183383 10501596900891636321275075)
    ·
      refine ⟨15752395351337454481912613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10501596900891636321275075 15752395351337454481912613)
      ·
        refine ⟨2953574128375772715358615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15752395351337454481912613 2953574128375772715358615)
        ·
          refine ⟨4430361192563659073037923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2953574128375772715358615 4430361192563659073037923)
          ·
            refine ⟨6645541788845488609556885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4430361192563659073037923 6645541788845488609556885)
            ·
              refine ⟨311509771352132278572979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6645541788845488609556885 311509771352132278572979)
              ·
                refine ⟨467264657028198417859469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311509771352132278572979 467264657028198417859469)
                ·
                  refine ⟨175224246385574406697301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467264657028198417859469 175224246385574406697301)
                  ·
                    rfl

theorem cell20_383904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_383904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383904 prefixEnd_383904 := by exact prefixLift 383904
  have htrace : WordTrace (prefixWord ++ tailWord_383904) baseStart_383904 baseEnd_383904 := by
    simpa [prefixWord, tailWord_383904, baseEnd_383904] using wordTrace_append hprefix tailTrace_383904
  have hstable : (prefixWord ++ tailWord_383904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383904).length < 2 ^ (prefixWord ++ tailWord_383904).sum := by decide
  have hdescent : baseEnd_383904 < baseStart_383904 := by decide
  rcases family_descends (prefixWord ++ tailWord_383904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383956 : List Nat := [2, 4, 1, 2, 1, 2, 3, 5]
def baseStart_383956 : Nat := 118140960795 + 383956 * 2 ^ 59
def prefixEnd_383956 : Nat := 4983230072969 + 3 ^ 40 * 383956 * 2
def baseEnd_383956 : Nat := 58415993534164445654585

theorem tailTrace_383956 : CollatzResearch.WordTrace tailWord_383956 prefixEnd_383956 58415993534164445654585 := by
  unfold tailWord_383956
  simp only [CollatzResearch.WordTrace]
  refine ⟨7002012898500230654629861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9336017198000307539506481 7002012898500230654629861)
  ·
    refine ⟨1312877418468793247743099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7002012898500230654629861 1312877418468793247743099)
    ·
      refine ⟨1969316127703189871614649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1312877418468793247743099 1969316127703189871614649)
      ·
        refine ⟨1476987095777392403710987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1969316127703189871614649 1476987095777392403710987)
        ·
          refine ⟨2215480643666088605566481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476987095777392403710987 2215480643666088605566481)
          ·
            refine ⟨1661610482749566454174861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2215480643666088605566481 1661610482749566454174861)
            ·
              refine ⟨623103931031087420315573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1661610482749566454174861 623103931031087420315573)
              ·
                refine ⟨58415993534164445654585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 623103931031087420315573 58415993534164445654585)
                ·
                  rfl

theorem cell20_383956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_383956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383956 prefixEnd_383956 := by exact prefixLift 383956
  have htrace : WordTrace (prefixWord ++ tailWord_383956) baseStart_383956 baseEnd_383956 := by
    simpa [prefixWord, tailWord_383956, baseEnd_383956] using wordTrace_append hprefix tailTrace_383956
  have hstable : (prefixWord ++ tailWord_383956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383956).length < 2 ^ (prefixWord ++ tailWord_383956).sum := by decide
  have hdescent : baseEnd_383956 < baseStart_383956 := by decide
  rcases family_descends (prefixWord ++ tailWord_383956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383984 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_383984 : Nat := 118140960795 + 383984 * 2 ^ 59
def prefixEnd_383984 : Nat := 4983230072969 + 3 ^ 40 * 383984 * 2
def baseEnd_383984 : Nat := 175260760565449684030307

theorem tailTrace_383984 : CollatzResearch.WordTrace tailWord_383984 prefixEnd_383984 175260760565449684030307 := by
  unfold tailWord_383984
  simp only [CollatzResearch.WordTrace]
  refine ⟨7002523520449511045639503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9336698027266014727519337 7002523520449511045639503)
  ·
    refine ⟨10503785280674266568459255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7002523520449511045639503 10503785280674266568459255)
    ·
      refine ⟨15755677921011399852688883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10503785280674266568459255 15755677921011399852688883)
      ·
        refine ⟨23633516881517099779033325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15755677921011399852688883 23633516881517099779033325)
        ·
          refine ⟨8862568830568912417137497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23633516881517099779033325 8862568830568912417137497)
          ·
            refine ⟨6646926622926684312853123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8862568830568912417137497 6646926622926684312853123)
            ·
              refine ⟨9970389934390026469279685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6646926622926684312853123 9970389934390026469279685)
              ·
                refine ⟨1869448112698129962989941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9970389934390026469279685 1869448112698129962989941)
                ·
                  refine ⟨175260760565449684030307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1869448112698129962989941 175260760565449684030307)
                  ·
                    rfl

theorem cell20_383984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_383984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_383984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_383984 prefixEnd_383984 := by exact prefixLift 383984
  have htrace : WordTrace (prefixWord ++ tailWord_383984) baseStart_383984 baseEnd_383984 := by
    simpa [prefixWord, tailWord_383984, baseEnd_383984] using wordTrace_append hprefix tailTrace_383984
  have hstable : (prefixWord ++ tailWord_383984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383984).length < 2 ^ (prefixWord ++ tailWord_383984).sum := by decide
  have hdescent : baseEnd_383984 < baseStart_383984 := by decide
  rcases family_descends (prefixWord ++ tailWord_383984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384001 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 5]
def baseStart_384001 : Nat := 118140960795 + 384001 * 2 ^ 59
def prefixEnd_384001 : Nat := 4983230072969 + 3 ^ 40 * 384001 * 2
def baseEnd_384001 : Nat := 175268519828673180463571

theorem tailTrace_384001 : CollatzResearch.WordTrace tailWord_384001 prefixEnd_384001 175268519828673180463571 := by
  unfold tailWord_384001
  simp only [CollatzResearch.WordTrace]
  refine ⟨14005667081837433994647857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9337111387891622663098571 14005667081837433994647857)
  ·
    refine ⟨10504250311378075495985893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14005667081837433994647857 10504250311378075495985893)
    ·
      refine ⟨1969546933383389155497355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10504250311378075495985893 1969546933383389155497355)
      ·
        refine ⟨2954320400075083733246033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1969546933383389155497355 2954320400075083733246033)
        ·
          refine ⟨2215740300056312799934525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2954320400075083733246033 2215740300056312799934525)
          ·
            refine ⟨830902612521117299975447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2215740300056312799934525 830902612521117299975447)
            ·
              refine ⟨1246353918781675949963171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830902612521117299975447 1246353918781675949963171)
              ·
                refine ⟨1869530878172513924944757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246353918781675949963171 1869530878172513924944757)
                ·
                  refine ⟨175268519828673180463571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1869530878172513924944757 175268519828673180463571)
                  ·
                    rfl

theorem cell20_384001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_384001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384001 prefixEnd_384001 := by exact prefixLift 384001
  have htrace : WordTrace (prefixWord ++ tailWord_384001) baseStart_384001 baseEnd_384001 := by
    simpa [prefixWord, tailWord_384001, baseEnd_384001] using wordTrace_append hprefix tailTrace_384001
  have hstable : (prefixWord ++ tailWord_384001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384001).length < 2 ^ (prefixWord ++ tailWord_384001).sum := by decide
  have hdescent : baseEnd_384001 < baseStart_384001 := by decide
  rcases family_descends (prefixWord ++ tailWord_384001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384008 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_384008 : Nat := 118140960795 + 384008 * 2 ^ 59
def prefixEnd_384008 : Nat := 4983230072969 + 3 ^ 40 * 384008 * 2
def baseEnd_384008 : Nat := 175271714819412267230209

theorem tailTrace_384008 : CollatzResearch.WordTrace tailWord_384008 prefixEnd_384008 175271714819412267230209 := by
  unfold tailWord_384008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7002961196406037095076339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9337281595208049460101785 7002961196406037095076339)
  ·
    refine ⟨10504441794609055642614509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7002961196406037095076339 10504441794609055642614509)
    ·
      refine ⟨3939165672978395865980441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10504441794609055642614509 3939165672978395865980441)
      ·
        refine ⟨2954374254733796899485331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3939165672978395865980441 2954374254733796899485331)
        ·
          refine ⟨4431561382100695349227997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2954374254733796899485331 4431561382100695349227997)
          ·
            refine ⟨1661835518287760755960499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4431561382100695349227997 1661835518287760755960499)
            ·
              refine ⟨2492753277431641133940749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661835518287760755960499 2492753277431641133940749)
              ·
                refine ⟨934782479036865425227781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2492753277431641133940749 934782479036865425227781)
                ·
                  refine ⟨175271714819412267230209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 934782479036865425227781 175271714819412267230209)
                  ·
                    rfl

theorem cell20_384008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_384008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384008 prefixEnd_384008 := by exact prefixLift 384008
  have htrace : WordTrace (prefixWord ++ tailWord_384008) baseStart_384008 baseEnd_384008 := by
    simpa [prefixWord, tailWord_384008, baseEnd_384008] using wordTrace_append hprefix tailTrace_384008
  have hstable : (prefixWord ++ tailWord_384008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384008).length < 2 ^ (prefixWord ++ tailWord_384008).sum := by decide
  have hdescent : baseEnd_384008 < baseStart_384008 := by decide
  rcases family_descends (prefixWord ++ tailWord_384008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384028 : List Nat := [2, 2, 3, 1, 5, 1, 2, 4]
def baseStart_384028 : Nat := 118140960795 + 384028 * 2 ^ 59
def prefixEnd_384028 : Nat := 4983230072969 + 3 ^ 40 * 384028 * 2
def baseEnd_384028 : Nat := 58426947788127028854487

theorem tailTrace_384028 : CollatzResearch.WordTrace tailWord_384028 prefixEnd_384028 58426947788127028854487 := by
  unfold tailWord_384028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7003325926369808802940369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9337767901826411737253825 7003325926369808802940369)
  ·
    refine ⟨5252494444777356602205277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7003325926369808802940369 5252494444777356602205277)
    ·
      refine ⟨1969685416791508725826979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5252494444777356602205277 1969685416791508725826979)
      ·
        refine ⟨2954528125187263088740469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1969685416791508725826979 2954528125187263088740469)
        ·
          refine ⟨276987011736305914569419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2954528125187263088740469 276987011736305914569419)
          ·
            refine ⟨415480517604458871854129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276987011736305914569419 415480517604458871854129)
            ·
              refine ⟨311610388203344153890597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415480517604458871854129 311610388203344153890597)
              ·
                refine ⟨58426947788127028854487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 311610388203344153890597 58426947788127028854487)
                ·
                  rfl

theorem cell20_384028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_384028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384028 prefixEnd_384028 := by exact prefixLift 384028
  have htrace : WordTrace (prefixWord ++ tailWord_384028) baseStart_384028 baseEnd_384028 := by
    simpa [prefixWord, tailWord_384028, baseEnd_384028] using wordTrace_append hprefix tailTrace_384028
  have hstable : (prefixWord ++ tailWord_384028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384028).length < 2 ^ (prefixWord ++ tailWord_384028).sum := by decide
  have hdescent : baseEnd_384028 < baseStart_384028 := by decide
  rcases family_descends (prefixWord ++ tailWord_384028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384084 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_384084 : Nat := 118140960795 + 384084 * 2 ^ 59
def prefixEnd_384084 : Nat := 4983230072969 + 3 ^ 40 * 384084 * 2
def baseEnd_384084 : Nat := 175306403290293780696565

theorem tailTrace_384084 : CollatzResearch.WordTrace tailWord_384084 prefixEnd_384084 175306403290293780696565 := by
  unfold tailWord_384084
  simp only [CollatzResearch.WordTrace]
  refine ⟨7004347170268369584959653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9339129560357826113279537 7004347170268369584959653)
  ·
    refine ⟨1313315094425319297179935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7004347170268369584959653 1313315094425319297179935)
    ·
      refine ⟨1969972641637978945769903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1313315094425319297179935 1969972641637978945769903)
      ·
        refine ⟨2954958962456968418654855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1969972641637978945769903 2954958962456968418654855)
        ·
          refine ⟨4432438443685452627982283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2954958962456968418654855 4432438443685452627982283)
          ·
            refine ⟨6648657665528178941973425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4432438443685452627982283 6648657665528178941973425)
            ·
              refine ⟨4986493249146134206480069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6648657665528178941973425 4986493249146134206480069)
              ·
                refine ⟨934967484214900163715013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4986493249146134206480069 934967484214900163715013)
                ·
                  refine ⟨175306403290293780696565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 934967484214900163715013 175306403290293780696565)
                  ·
                    rfl

theorem cell20_384084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_384084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384084 prefixEnd_384084 := by exact prefixLift 384084
  have htrace : WordTrace (prefixWord ++ tailWord_384084) baseStart_384084 baseEnd_384084 := by
    simpa [prefixWord, tailWord_384084, baseEnd_384084] using wordTrace_append hprefix tailTrace_384084
  have hstable : (prefixWord ++ tailWord_384084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384084).length < 2 ^ (prefixWord ++ tailWord_384084).sum := by decide
  have hdescent : baseEnd_384084 < baseStart_384084 := by decide
  rcases family_descends (prefixWord ++ tailWord_384084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384101 : List Nat := [1, 3, 1, 3, 2, 1, 2, 5, 2]
def baseStart_384101 : Nat := 118140960795 + 384101 * 2 ^ 59
def prefixEnd_384101 : Nat := 4983230072969 + 3 ^ 40 * 384101 * 2
def baseEnd_384101 : Nat := 175314162553517277129829

theorem tailTrace_384101 : CollatzResearch.WordTrace tailWord_384101 prefixEnd_384101 175314162553517277129829 := by
  unfold tailWord_384101
  simp only [CollatzResearch.WordTrace]
  refine ⟨14009314381475151073288157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9339542920983434048858771 14009314381475151073288157)
  ·
    refine ⟨5253492893053181652483059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14009314381475151073288157 5253492893053181652483059)
    ·
      refine ⟨7880239339579772478724589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5253492893053181652483059 7880239339579772478724589)
      ·
        refine ⟨2955089752342414679521721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7880239339579772478724589 2955089752342414679521721)
        ·
          refine ⟨2216317314256811009641291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2955089752342414679521721 2216317314256811009641291)
          ·
            refine ⟨3324475971385216514461937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216317314256811009641291 3324475971385216514461937)
            ·
              refine ⟨2493356978538912385846453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3324475971385216514461937 2493356978538912385846453)
              ·
                refine ⟨233752216738023036173105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2493356978538912385846453 233752216738023036173105)
                ·
                  refine ⟨175314162553517277129829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233752216738023036173105 175314162553517277129829)
                  ·
                    rfl

theorem cell20_384101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_384101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384101 prefixEnd_384101 := by exact prefixLift 384101
  have htrace : WordTrace (prefixWord ++ tailWord_384101) baseStart_384101 baseEnd_384101 := by
    simpa [prefixWord, tailWord_384101, baseEnd_384101] using wordTrace_append hprefix tailTrace_384101
  have hstable : (prefixWord ++ tailWord_384101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384101).length < 2 ^ (prefixWord ++ tailWord_384101).sum := by decide
  have hdescent : baseEnd_384101 < baseStart_384101 := by decide
  rcases family_descends (prefixWord ++ tailWord_384101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384118 : List Nat := [5, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_384118 : Nat := 118140960795 + 384118 * 2 ^ 59
def prefixEnd_384118 : Nat := 4983230072969 + 3 ^ 40 * 384118 * 2
def baseEnd_384118 : Nat := 175321921816740773563093

theorem tailTrace_384118 : CollatzResearch.WordTrace tailWord_384118 prefixEnd_384118 175321921816740773563093 := by
  unfold tailWord_384118
  simp only [CollatzResearch.WordTrace]
  refine ⟨875620901400847686041063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9339956281609041984438005 875620901400847686041063)
  ·
    refine ⟨1313431352101271529061595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 875620901400847686041063 1313431352101271529061595)
    ·
      refine ⟨1970147028151907293592393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1313431352101271529061595 1970147028151907293592393)
      ·
        refine ⟨1477610271113930470194295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1970147028151907293592393 1477610271113930470194295)
        ·
          refine ⟨2216415406670895705291443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477610271113930470194295 2216415406670895705291443)
          ·
            refine ⟨3324623110006343557937165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216415406670895705291443 3324623110006343557937165)
            ·
              refine ⟨1246733666252378834226437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3324623110006343557937165 1246733666252378834226437)
              ·
                refine ⟨233762562422321031417457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1246733666252378834226437 233762562422321031417457)
                ·
                  refine ⟨175321921816740773563093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233762562422321031417457 175321921816740773563093)
                  ·
                    rfl

theorem cell20_384118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_384118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_384118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_384118 prefixEnd_384118 := by exact prefixLift 384118
  have htrace : WordTrace (prefixWord ++ tailWord_384118) baseStart_384118 baseEnd_384118 := by
    simpa [prefixWord, tailWord_384118, baseEnd_384118] using wordTrace_append hprefix tailTrace_384118
  have hstable : (prefixWord ++ tailWord_384118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384118).length < 2 ^ (prefixWord ++ tailWord_384118).sum := by decide
  have hdescent : baseEnd_384118 < baseStart_384118 := by decide
  rcases family_descends (prefixWord ++ tailWord_384118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
