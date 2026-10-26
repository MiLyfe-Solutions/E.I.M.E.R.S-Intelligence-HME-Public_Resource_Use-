import V185TrunkScan20Chunk160

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_979514 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_979514 : Nat := 118140960795 + 979514 * 2 ^ 59
def prefixEnd_979514 : Nat := 4983230072969 + 3 ^ 40 * 979514 * 2
def baseEnd_979514 : Nat := 447076879829498560595825

theorem tailTrace_979514 : CollatzResearch.WordTrace tailWord_979514 prefixEnd_979514 447076879829498560595825 := by
  unfold tailWord_979514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8931452643348885129464399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23817207048930360345238397 8931452643348885129464399)
  ·
    refine ⟨13397178965023327694196599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8931452643348885129464399 13397178965023327694196599)
    ·
      refine ⟨20095768447534991541294899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13397178965023327694196599 20095768447534991541294899)
      ·
        refine ⟨30143652671302487311942349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20095768447534991541294899 30143652671302487311942349)
        ·
          refine ⟨11303869751738432741978381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30143652671302487311942349 11303869751738432741978381)
          ·
            refine ⟨4238951156901912278241893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11303869751738432741978381 4238951156901912278241893)
            ·
              refine ⟨794803341919108552170355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4238951156901912278241893 794803341919108552170355)
              ·
                refine ⟨1192205012878662828255533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794803341919108552170355 1192205012878662828255533)
                ·
                  refine ⟨447076879829498560595825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192205012878662828255533 447076879829498560595825)
                  ·
                    rfl

theorem cell20_979514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_979514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979514 prefixEnd_979514 := by exact prefixLift 979514
  have htrace : WordTrace (prefixWord ++ tailWord_979514) baseStart_979514 baseEnd_979514 := by
    simpa [prefixWord, tailWord_979514, baseEnd_979514] using wordTrace_append hprefix tailTrace_979514
  have hstable : (prefixWord ++ tailWord_979514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979514).length < 2 ^ (prefixWord ++ tailWord_979514).sum := by decide
  have hdescent : baseEnd_979514 < baseStart_979514 := by decide
  rcases family_descends (prefixWord ++ tailWord_979514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979549 : List Nat := [1, 4, 4, 11]
def baseStart_979549 : Nat := 118140960795 + 979549 * 2 ^ 59
def prefixEnd_979549 : Nat := 4983230072969 + 3 ^ 40 * 979549 * 2
def baseEnd_979549 : Nat := 1839888291288864174605

theorem tailTrace_979549 : CollatzResearch.WordTrace tailWord_979549 prefixEnd_979549 1839888291288864174605 := by
  unfold tailWord_979549
  simp only [CollatzResearch.WordTrace]
  refine ⟨35727087128268741495381701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23818058085512494330254467 35727087128268741495381701)
  ·
    refine ⟨6698828836550389030384069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35727087128268741495381701 6698828836550389030384069)
    ·
      refine ⟨1256030406853197943197013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6698828836550389030384069 1256030406853197943197013)
      ·
        refine ⟨1839888291288864174605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1256030406853197943197013 1839888291288864174605)
        ·
          rfl

theorem cell20_979549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 11].length) (baseStart_979549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979549 prefixEnd_979549 := by exact prefixLift 979549
  have htrace : WordTrace (prefixWord ++ tailWord_979549) baseStart_979549 baseEnd_979549 := by
    simpa [prefixWord, tailWord_979549, baseEnd_979549] using wordTrace_append hprefix tailTrace_979549
  have hstable : (prefixWord ++ tailWord_979549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979549).length < 2 ^ (prefixWord ++ tailWord_979549).sum := by decide
  have hdescent : baseEnd_979549 < baseStart_979549 := by decide
  rcases family_descends (prefixWord ++ tailWord_979549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979566 : List Nat := [4, 1, 2, 2, 2, 1, 3, 5]
def baseStart_979566 : Nat := 118140960795 + 979566 * 2 ^ 59
def prefixEnd_979566 : Nat := 4983230072969 + 3 ^ 40 * 979566 * 2
def baseEnd_979566 : Nat := 149033538015472496954093

theorem tailTrace_979566 : CollatzResearch.WordTrace tailWord_979566 prefixEnd_979566 149033538015472496954093 := by
  unfold tailWord_979566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465963396150894174843819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23818471446138102265833701 4465963396150894174843819)
  ·
    refine ⟨6698945094226341262265729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4465963396150894174843819 6698945094226341262265729)
    ·
      refine ⟨5024208820669755946699297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6698945094226341262265729 5024208820669755946699297)
      ·
        refine ⟨3768156615502316960024473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5024208820669755946699297 3768156615502316960024473)
        ·
          refine ⟨2826117461626737720018355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3768156615502316960024473 2826117461626737720018355)
          ·
            refine ⟨4239176192440106580027533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826117461626737720018355 4239176192440106580027533)
            ·
              refine ⟨1589691072165039967510325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4239176192440106580027533 1589691072165039967510325)
              ·
                refine ⟨149033538015472496954093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1589691072165039967510325 149033538015472496954093)
                ·
                  rfl

theorem cell20_979566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_979566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979566 prefixEnd_979566 := by exact prefixLift 979566
  have htrace : WordTrace (prefixWord ++ tailWord_979566) baseStart_979566 baseEnd_979566 := by
    simpa [prefixWord, tailWord_979566, baseEnd_979566] using wordTrace_append hprefix tailTrace_979566
  have hstable : (prefixWord ++ tailWord_979566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979566).length < 2 ^ (prefixWord ++ tailWord_979566).sum := by decide
  have hdescent : baseEnd_979566 < baseStart_979566 := by decide
  rcases family_descends (prefixWord ++ tailWord_979566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979604 : List Nat := [2, 4, 2, 2, 1, 2, 7]
def baseStart_979604 : Nat := 118140960795 + 979604 * 2 ^ 59
def prefixEnd_979604 : Nat := 4983230072969 + 3 ^ 40 * 979604 * 2
def baseEnd_979604 : Nat := 49679773142428694177273

theorem tailTrace_979604 : CollatzResearch.WordTrace tailWord_979604 prefixEnd_979604 49679773142428694177273 := by
  unfold tailWord_979604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17864546571534742944316933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23819395428712990592422577 17864546571534742944316933)
  ·
    refine ⟨3349602482162764302059425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17864546571534742944316933 3349602482162764302059425)
    ·
      refine ⟨2512201861622073226544569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3349602482162764302059425 2512201861622073226544569)
      ·
        refine ⟨1884151396216554919908427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2512201861622073226544569 1884151396216554919908427)
        ·
          refine ⟨2826227094324832379862641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884151396216554919908427 2826227094324832379862641)
          ·
            refine ⟨2119670320743624284896981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2826227094324832379862641 2119670320743624284896981)
            ·
              refine ⟨49679773142428694177273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2119670320743624284896981 49679773142428694177273)
              ·
                rfl

theorem cell20_979604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 7].length) (baseStart_979604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979604 prefixEnd_979604 := by exact prefixLift 979604
  have htrace : WordTrace (prefixWord ++ tailWord_979604) baseStart_979604 baseEnd_979604 := by
    simpa [prefixWord, tailWord_979604, baseEnd_979604] using wordTrace_append hprefix tailTrace_979604
  have hstable : (prefixWord ++ tailWord_979604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979604).length < 2 ^ (prefixWord ++ tailWord_979604).sum := by decide
  have hdescent : baseEnd_979604 < baseStart_979604 := by decide
  rcases family_descends (prefixWord ++ tailWord_979604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979614 : List Nat := [4, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_979614 : Nat := 118140960795 + 979614 * 2 ^ 59
def prefixEnd_979614 : Nat := 4983230072969 + 3 ^ 40 * 979614 * 2
def baseEnd_979614 : Nat := 447122522554342657262083

theorem tailTrace_979614 : CollatzResearch.WordTrace tailWord_979614 prefixEnd_979614 447122522554342657262083 := by
  unfold tailWord_979614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4466182234129157199562237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23819638582022171730998597 4466182234129157199562237)
  ·
    refine ⟨1674818337798433949835839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4466182234129157199562237 1674818337798433949835839)
    ·
      refine ⟨2512227506697650924753759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674818337798433949835839 2512227506697650924753759)
      ·
        refine ⟨3768341260046476387130639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2512227506697650924753759 3768341260046476387130639)
        ·
          refine ⟨5652511890069714580695959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768341260046476387130639 5652511890069714580695959)
          ·
            refine ⟨8478767835104571871043939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652511890069714580695959 8478767835104571871043939)
            ·
              refine ⟨12718151752656857806565909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478767835104571871043939 12718151752656857806565909)
              ·
                refine ⟨596163363405790209682777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12718151752656857806565909 596163363405790209682777)
                ·
                  refine ⟨447122522554342657262083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596163363405790209682777 447122522554342657262083)
                  ·
                    rfl

theorem cell20_979614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_979614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979614 prefixEnd_979614 := by exact prefixLift 979614
  have htrace : WordTrace (prefixWord ++ tailWord_979614) baseStart_979614 baseEnd_979614 := by
    simpa [prefixWord, tailWord_979614, baseEnd_979614] using wordTrace_append hprefix tailTrace_979614
  have hstable : (prefixWord ++ tailWord_979614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979614).length < 2 ^ (prefixWord ++ tailWord_979614).sum := by decide
  have hdescent : baseEnd_979614 < baseStart_979614 := by decide
  rcases family_descends (prefixWord ++ tailWord_979614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979652 : List Nat := [2, 3, 3, 1, 1, 2, 3, 3, 2]
def baseStart_979652 : Nat := 118140960795 + 979652 * 2 ^ 59
def prefixEnd_979652 : Nat := 4983230072969 + 3 ^ 40 * 979652 * 2
def baseEnd_979652 : Nat := 447139866789783413995261

theorem tailTrace_979652 : CollatzResearch.WordTrace tailWord_979652 prefixEnd_979652 447139866789783413995261 := by
  unfold tailWord_979652
  simp only [CollatzResearch.WordTrace]
  refine ⟨17865421923447795043190605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23820562564597060057587473 17865421923447795043190605)
  ·
    refine ⟨6699533221292923141196477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17865421923447795043190605 6699533221292923141196477)
    ·
      refine ⟨2512324957984846177948679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6699533221292923141196477 2512324957984846177948679)
      ·
        refine ⟨3768487436977269266923019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2512324957984846177948679 3768487436977269266923019)
        ·
          refine ⟨5652731155465903900384529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768487436977269266923019 5652731155465903900384529)
          ·
            refine ⟨4239548366599427925288397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5652731155465903900384529 4239548366599427925288397)
            ·
              refine ⟨1589830637474785471983149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4239548366599427925288397 1589830637474785471983149)
              ·
                refine ⟨596186489053044551993681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1589830637474785471983149 596186489053044551993681)
                ·
                  refine ⟨447139866789783413995261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596186489053044551993681 447139866789783413995261)
                  ·
                    rfl

theorem cell20_979652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_979652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979652 prefixEnd_979652 := by exact prefixLift 979652
  have htrace : WordTrace (prefixWord ++ tailWord_979652) baseStart_979652 baseEnd_979652 := by
    simpa [prefixWord, tailWord_979652, baseEnd_979652] using wordTrace_append hprefix tailTrace_979652
  have hstable : (prefixWord ++ tailWord_979652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979652).length < 2 ^ (prefixWord ++ tailWord_979652).sum := by decide
  have hdescent : baseEnd_979652 < baseStart_979652 := by decide
  rcases family_descends (prefixWord ++ tailWord_979652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979669 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 4]
def baseStart_979669 : Nat := 118140960795 + 979669 * 2 ^ 59
def prefixEnd_979669 : Nat := 4983230072969 + 3 ^ 40 * 979669 * 2
def baseEnd_979669 : Nat := 447147626053006910428525

theorem tailTrace_979669 : CollatzResearch.WordTrace tailWord_979669 prefixEnd_979669 447147626053006910428525 := by
  unfold tailWord_979669
  simp only [CollatzResearch.WordTrace]
  refine ⟨35731463887834001989750061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23820975925222667993166707 35731463887834001989750061)
  ·
    refine ⟨13399298957937750746156273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35731463887834001989750061 13399298957937750746156273)
    ·
      refine ⟨10049474218453313059617205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13399298957937750746156273 10049474218453313059617205)
      ·
        refine ⟨942138207979998099339113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10049474218453313059617205 942138207979998099339113)
        ·
          refine ⟨706603655984998574504335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 942138207979998099339113 706603655984998574504335)
          ·
            refine ⟨1059905483977497861756503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706603655984998574504335 1059905483977497861756503)
            ·
              refine ⟨1589858225966246792634755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059905483977497861756503 1589858225966246792634755)
              ·
                refine ⟨2384787338949370188952133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589858225966246792634755 2384787338949370188952133)
                ·
                  refine ⟨447147626053006910428525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2384787338949370188952133 447147626053006910428525)
                  ·
                    rfl

theorem cell20_979669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_979669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979669 prefixEnd_979669 := by exact prefixLift 979669
  have htrace : WordTrace (prefixWord ++ tailWord_979669) baseStart_979669 baseEnd_979669 := by
    simpa [prefixWord, tailWord_979669, baseEnd_979669] using wordTrace_append hprefix tailTrace_979669
  have hstable : (prefixWord ++ tailWord_979669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979669).length < 2 ^ (prefixWord ++ tailWord_979669).sum := by decide
  have hdescent : baseEnd_979669 < baseStart_979669 := by decide
  rcases family_descends (prefixWord ++ tailWord_979669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979683 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 3]
def baseStart_979683 : Nat := 118140960795 + 979683 * 2 ^ 59
def prefixEnd_979683 : Nat := 4983230072969 + 3 ^ 40 * 979683 * 2
def baseEnd_979683 : Nat := 447154016034485083961801

theorem tailTrace_979683 : CollatzResearch.WordTrace tailWord_979683 prefixEnd_979683 447154016034485083961801 := by
  unfold tailWord_979683
  simp only [CollatzResearch.WordTrace]
  refine ⟨35731974509783282380759703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23821316339855521587173135 35731974509783282380759703)
  ·
    refine ⟨53597961764674923571139555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35731974509783282380759703 53597961764674923571139555)
    ·
      refine ⟨80396942647012385356709333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53597961764674923571139555 80396942647012385356709333)
      ·
        refine ⟨1884303343289352781797875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 80396942647012385356709333 1884303343289352781797875)
        ·
          refine ⟨2826455014934029172696813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884303343289352781797875 2826455014934029172696813)
          ·
            refine ⟨1059920630600260939761305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2826455014934029172696813 1059920630600260939761305)
            ·
              refine ⟨794940472950195704820979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059920630600260939761305 794940472950195704820979)
              ·
                refine ⟨1192410709425293557231469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794940472950195704820979 1192410709425293557231469)
                ·
                  refine ⟨447154016034485083961801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192410709425293557231469 447154016034485083961801)
                  ·
                    rfl

theorem cell20_979683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 3].length) (baseStart_979683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979683 prefixEnd_979683 := by exact prefixLift 979683
  have htrace : WordTrace (prefixWord ++ tailWord_979683) baseStart_979683 baseEnd_979683 := by
    simpa [prefixWord, tailWord_979683, baseEnd_979683] using wordTrace_append hprefix tailTrace_979683
  have hstable : (prefixWord ++ tailWord_979683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979683).length < 2 ^ (prefixWord ++ tailWord_979683).sum := by decide
  have hdescent : baseEnd_979683 < baseStart_979683 := by decide
  rcases family_descends (prefixWord ++ tailWord_979683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979735 : List Nat := [1, 1, 3, 4, 4, 1, 1, 5]
def baseStart_979735 : Nat := 118140960795 + 979735 * 2 ^ 59
def prefixEnd_979735 : Nat := 4983230072969 + 3 ^ 40 * 979735 * 2
def baseEnd_979735 : Nat := 149059250083801338076085

theorem tailTrace_979735 : CollatzResearch.WordTrace tailWord_979735 prefixEnd_979735 149059250083801338076085 := by
  unfold tailWord_979735
  simp only [CollatzResearch.WordTrace]
  refine ⟨35733871105594895261652659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23822580737063263507768439 35733871105594895261652659)
  ·
    refine ⟨53600806658392342892478989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35733871105594895261652659 53600806658392342892478989)
    ·
      refine ⟨20100302496897128584679621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53600806658392342892478989 20100302496897128584679621)
      ·
        refine ⟨3768806718168211609627429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20100302496897128584679621 3768806718168211609627429)
        ·
          refine ⟨706651259656539676805143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3768806718168211609627429 706651259656539676805143)
          ·
            refine ⟨1059976889484809515207715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706651259656539676805143 1059976889484809515207715)
            ·
              refine ⟨1589965334227214272811573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059976889484809515207715 1589965334227214272811573)
              ·
                refine ⟨149059250083801338076085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1589965334227214272811573 149059250083801338076085)
                ·
                  rfl

theorem cell20_979735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 5].length) (baseStart_979735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979735 prefixEnd_979735 := by exact prefixLift 979735
  have htrace : WordTrace (prefixWord ++ tailWord_979735) baseStart_979735 baseEnd_979735 := by
    simpa [prefixWord, tailWord_979735, baseEnd_979735] using wordTrace_append hprefix tailTrace_979735
  have hstable : (prefixWord ++ tailWord_979735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979735).length < 2 ^ (prefixWord ++ tailWord_979735).sum := by decide
  have hdescent : baseEnd_979735 < baseStart_979735 := by decide
  rcases family_descends (prefixWord ++ tailWord_979735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979753 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_979753 : Nat := 118140960795 + 979753 * 2 ^ 59
def prefixEnd_979753 : Nat := 4983230072969 + 3 ^ 40 * 979753 * 2
def baseEnd_979753 : Nat := 447185965941875951628181

theorem tailTrace_979753 : CollatzResearch.WordTrace tailWord_979753 prefixEnd_979753 447185965941875951628181 := by
  unfold tailWord_979753
  simp only [CollatzResearch.WordTrace]
  refine ⟨35734527619529684335807913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23823018413019789557205275 35734527619529684335807913)
  ·
    refine ⟨26800895714647263251855935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35734527619529684335807913 26800895714647263251855935)
    ·
      refine ⟨40201343571970894877783903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26800895714647263251855935 40201343571970894877783903)
      ·
        refine ⟨60302015357956342316675855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40201343571970894877783903 60302015357956342316675855)
        ·
          refine ⟨90453023036934513475013783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60302015357956342316675855 90453023036934513475013783)
          ·
            refine ⟨135679534555401770212520675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90453023036934513475013783 135679534555401770212520675)
            ·
              refine ⟨203519301833102655318781013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135679534555401770212520675 203519301833102655318781013)
              ·
                refine ⟨2384991818356671742016965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 203519301833102655318781013 2384991818356671742016965)
                ·
                  refine ⟨447185965941875951628181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2384991818356671742016965 447185965941875951628181)
                  ·
                    rfl

theorem cell20_979753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_979753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979753 prefixEnd_979753 := by exact prefixLift 979753
  have htrace : WordTrace (prefixWord ++ tailWord_979753) baseStart_979753 baseEnd_979753 := by
    simpa [prefixWord, tailWord_979753, baseEnd_979753] using wordTrace_append hprefix tailTrace_979753
  have hstable : (prefixWord ++ tailWord_979753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979753).length < 2 ^ (prefixWord ++ tailWord_979753).sum := by decide
  have hdescent : baseEnd_979753 < baseStart_979753 := by decide
  rcases family_descends (prefixWord ++ tailWord_979753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979760 : List Nat := [2, 1, 1, 1, 2, 2, 1, 10]
def baseStart_979760 : Nat := 118140960795 + 979760 * 2 ^ 59
def prefixEnd_979760 : Nat := 4983230072969 + 3 ^ 40 * 979760 * 2
def baseEnd_979760 : Nat := 149063053644205012798273

theorem tailTrace_979760 : CollatzResearch.WordTrace tailWord_979760 prefixEnd_979760 149063053644205012798273 := by
  unfold tailWord_979760
  simp only [CollatzResearch.WordTrace]
  refine ⟨17867391465252162265656367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23823188620336216354208489 17867391465252162265656367)
  ·
    refine ⟨26801087197878243398484551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17867391465252162265656367 26801087197878243398484551)
    ·
      refine ⟨40201630796817365097726827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26801087197878243398484551 40201630796817365097726827)
      ·
        refine ⟨60302446195226047646590241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40201630796817365097726827 60302446195226047646590241)
        ·
          refine ⟨45226834646419535734942681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60302446195226047646590241 45226834646419535734942681)
          ·
            refine ⟨33920125984814651801207011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45226834646419535734942681 33920125984814651801207011)
            ·
              refine ⟨50880188977221977701810517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33920125984814651801207011 50880188977221977701810517)
              ·
                refine ⟨149063053644205012798273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50880188977221977701810517 149063053644205012798273)
                ·
                  rfl

theorem cell20_979760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_979760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979760 prefixEnd_979760 := by exact prefixLift 979760
  have htrace : WordTrace (prefixWord ++ tailWord_979760) baseStart_979760 baseEnd_979760 := by
    simpa [prefixWord, tailWord_979760, baseEnd_979760] using wordTrace_append hprefix tailTrace_979760
  have hstable : (prefixWord ++ tailWord_979760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979760).length < 2 ^ (prefixWord ++ tailWord_979760).sum := by decide
  have hdescent : baseEnd_979760 < baseStart_979760 := by decide
  rcases family_descends (prefixWord ++ tailWord_979760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979784 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_979784 : Nat := 118140960795 + 979784 * 2 ^ 59
def prefixEnd_979784 : Nat := 4983230072969 + 3 ^ 40 * 979784 * 2
def baseEnd_979784 : Nat := 447200115186577621594721

theorem tailTrace_979784 : CollatzResearch.WordTrace tailWord_979784 prefixEnd_979784 447200115186577621594721 := by
  unfold tailWord_979784
  simp only [CollatzResearch.WordTrace]
  refine ⟨17867829141208688315093203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23823772188278251086790937 17867829141208688315093203)
  ·
    refine ⟨26801743711813032472639805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17867829141208688315093203 26801743711813032472639805)
    ·
      refine ⟨10050653891929887177239927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26801743711813032472639805 10050653891929887177239927)
      ·
        refine ⟨15075980837894830765859891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10050653891929887177239927 15075980837894830765859891)
        ·
          refine ⟨22613971256842246148789837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15075980837894830765859891 22613971256842246148789837)
          ·
            refine ⟨8480239221315842305796189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22613971256842246148789837 8480239221315842305796189)
            ·
              refine ⟨3180089707993440864673571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8480239221315842305796189 3180089707993440864673571)
              ·
                refine ⟨4770134561990161297010357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180089707993440864673571 4770134561990161297010357)
                ·
                  refine ⟨447200115186577621594721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4770134561990161297010357 447200115186577621594721)
                  ·
                    rfl

theorem cell20_979784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_979784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979784 prefixEnd_979784 := by exact prefixLift 979784
  have htrace : WordTrace (prefixWord ++ tailWord_979784) baseStart_979784 baseEnd_979784 := by
    simpa [prefixWord, tailWord_979784, baseEnd_979784] using wordTrace_append hprefix tailTrace_979784
  have hstable : (prefixWord ++ tailWord_979784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979784).length < 2 ^ (prefixWord ++ tailWord_979784).sum := by decide
  have hdescent : baseEnd_979784 < baseStart_979784 := by decide
  rcases family_descends (prefixWord ++ tailWord_979784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979815 : List Nat := [1, 1, 5, 1, 2, 3, 1, 6]
def baseStart_979815 : Nat := 118140960795 + 979815 * 2 ^ 59
def prefixEnd_979815 : Nat := 4983230072969 + 3 ^ 40 * 979815 * 2
def baseEnd_979815 : Nat := 149071421477093097187087

theorem tailTrace_979815 : CollatzResearch.WordTrace tailWord_979815 prefixEnd_979815 149071421477093097187087 := by
  unfold tailWord_979815
  simp only [CollatzResearch.WordTrace]
  refine ⟨35736788945305068924564899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23824525963536712616376599 35736788945305068924564899)
  ·
    refine ⟨53605183417957603386847349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35736788945305068924564899 53605183417957603386847349)
    ·
      refine ⟨5025485945433525317516939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53605183417957603386847349 5025485945433525317516939)
      ·
        refine ⟨7538228918150287976275409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025485945433525317516939 7538228918150287976275409)
        ·
          refine ⟨5653671688612715982206557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7538228918150287976275409 5653671688612715982206557)
          ·
            refine ⟨2120126883229768493327459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5653671688612715982206557 2120126883229768493327459)
            ·
              refine ⟨3180190324844652739991189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120126883229768493327459 3180190324844652739991189)
              ·
                refine ⟨149071421477093097187087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3180190324844652739991189 149071421477093097187087)
                ·
                  rfl

theorem cell20_979815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_979815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979815 prefixEnd_979815 := by exact prefixLift 979815
  have htrace : WordTrace (prefixWord ++ tailWord_979815) baseStart_979815 baseEnd_979815 := by
    simpa [prefixWord, tailWord_979815, baseEnd_979815] using wordTrace_append hprefix tailTrace_979815
  have hstable : (prefixWord ++ tailWord_979815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979815).length < 2 ^ (prefixWord ++ tailWord_979815).sum := by decide
  have hdescent : baseEnd_979815 < baseStart_979815 := by decide
  rcases family_descends (prefixWord ++ tailWord_979815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979825 : List Nat := [1, 2, 2, 2, 1, 4, 3, 3, 2]
def baseStart_979825 : Nat := 118140960795 + 979825 * 2 ^ 59
def prefixEnd_979825 : Nat := 4983230072969 + 3 ^ 40 * 979825 * 2
def baseEnd_979825 : Nat := 447218828703763701227887

theorem tailTrace_979825 : CollatzResearch.WordTrace tailWord_979825 prefixEnd_979825 447218828703763701227887 := by
  unfold tailWord_979825
  simp only [CollatzResearch.WordTrace]
  refine ⟨35737153675268840632428929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23824769116845893754952619 35737153675268840632428929)
  ·
    refine ⟨26802865256451630474321697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35737153675268840632428929 26802865256451630474321697)
    ·
      refine ⟨20102148942338722855741273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26802865256451630474321697 20102148942338722855741273)
      ·
        refine ⟨15076611706754042141805955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20102148942338722855741273 15076611706754042141805955)
        ·
          refine ⟨22614917560131063212708933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15076611706754042141805955 22614917560131063212708933)
          ·
            refine ⟨4240297042524574352382925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22614917560131063212708933 4240297042524574352382925)
            ·
              refine ⟨1590111390946715382143597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4240297042524574352382925 1590111390946715382143597)
              ·
                refine ⟨596291771605018268303849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1590111390946715382143597 596291771605018268303849)
                ·
                  refine ⟨447218828703763701227887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596291771605018268303849 447218828703763701227887)
                  ·
                    rfl

theorem cell20_979825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_979825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979825 prefixEnd_979825 := by exact prefixLift 979825
  have htrace : WordTrace (prefixWord ++ tailWord_979825) baseStart_979825 baseEnd_979825 := by
    simpa [prefixWord, tailWord_979825, baseEnd_979825] using wordTrace_append hprefix tailTrace_979825
  have hstable : (prefixWord ++ tailWord_979825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979825).length < 2 ^ (prefixWord ++ tailWord_979825).sum := by decide
  have hdescent : baseEnd_979825 < baseStart_979825 := by decide
  rcases family_descends (prefixWord ++ tailWord_979825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979838 : List Nat := [4, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_979838 : Nat := 118140960795 + 979838 * 2 ^ 59
def prefixEnd_979838 : Nat := 4983230072969 + 3 ^ 40 * 979838 * 2
def baseEnd_979838 : Nat := 447224762257993433794501

theorem tailTrace_979838 : CollatzResearch.WordTrace tailWord_979838 prefixEnd_979838 447224762257993433794501 := by
  unfold tailWord_979838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467203478027717981581521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23825085216147829235101445 4467203478027717981581521)
  ·
    refine ⟨3350402608520788486186141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4467203478027717981581521 3350402608520788486186141)
    ·
      refine ⟨1256400978195295682319803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3350402608520788486186141 1256400978195295682319803)
      ·
        refine ⟨1884601467292943523479705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256400978195295682319803 1884601467292943523479705)
        ·
          refine ⟨1413451100469707642609779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1884601467292943523479705 1413451100469707642609779)
          ·
            refine ⟨2120176650704561463914669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413451100469707642609779 2120176650704561463914669)
            ·
              refine ⟨795066244014210548968001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2120176650704561463914669 795066244014210548968001)
              ·
                refine ⟨596299683010657911726001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795066244014210548968001 596299683010657911726001)
                ·
                  refine ⟨447224762257993433794501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596299683010657911726001 447224762257993433794501)
                  ·
                    rfl

theorem cell20_979838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_979838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979838 prefixEnd_979838 := by exact prefixLift 979838
  have htrace : WordTrace (prefixWord ++ tailWord_979838) baseStart_979838 baseEnd_979838 := by
    simpa [prefixWord, tailWord_979838, baseEnd_979838] using wordTrace_append hprefix tailTrace_979838
  have hstable : (prefixWord ++ tailWord_979838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979838).length < 2 ^ (prefixWord ++ tailWord_979838).sum := by decide
  have hdescent : baseEnd_979838 < baseStart_979838 := by decide
  rcases family_descends (prefixWord ++ tailWord_979838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979922 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_979922 : Nat := 118140960795 + 979922 * 2 ^ 59
def prefixEnd_979922 : Nat := 4983230072969 + 3 ^ 40 * 979922 * 2
def baseEnd_979922 : Nat := 447263102146862474994157

theorem tailTrace_979922 : CollatzResearch.WordTrace tailWord_979922 prefixEnd_979922 447263102146862474994157 := by
  unfold tailWord_979922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8935172888979356549677505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23827127703944950799140013 8935172888979356549677505)
  ·
    refine ⟨6701379666734517412258129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8935172888979356549677505 6701379666734517412258129)
    ·
      refine ⟨5026034750050888059193597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6701379666734517412258129 5026034750050888059193597)
      ·
        refine ⟨1884763031269083022197599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5026034750050888059193597 1884763031269083022197599)
        ·
          refine ⟨2827144546903624533296399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884763031269083022197599 2827144546903624533296399)
          ·
            refine ⟨4240716820355436799944599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827144546903624533296399 4240716820355436799944599)
            ·
              refine ⟨6361075230533155199916899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240716820355436799944599 6361075230533155199916899)
              ·
                refine ⟨9541612845799732799875349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361075230533155199916899 9541612845799732799875349)
                ·
                  refine ⟨447263102146862474994157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9541612845799732799875349 447263102146862474994157)
                  ·
                    rfl

theorem cell20_979922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_979922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979922 prefixEnd_979922 := by exact prefixLift 979922
  have htrace : WordTrace (prefixWord ++ tailWord_979922) baseStart_979922 baseEnd_979922 := by
    simpa [prefixWord, tailWord_979922, baseEnd_979922] using wordTrace_append hprefix tailTrace_979922
  have hstable : (prefixWord ++ tailWord_979922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979922).length < 2 ^ (prefixWord ++ tailWord_979922).sum := by decide
  have hdescent : baseEnd_979922 < baseStart_979922 := by decide
  rcases family_descends (prefixWord ++ tailWord_979922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979939 : List Nat := [1, 1, 1, 6, 1, 1, 4, 3, 2]
def baseStart_979939 : Nat := 118140960795 + 979939 * 2 ^ 59
def prefixEnd_979939 : Nat := 4983230072969 + 3 ^ 40 * 979939 * 2
def baseEnd_979939 : Nat := 447270861410085971427421

theorem tailTrace_979939 : CollatzResearch.WordTrace tailWord_979939 prefixEnd_979939 447270861410085971427421 := by
  unfold tailWord_979939
  simp only [CollatzResearch.WordTrace]
  refine ⟨35741311596855838102078871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23827541064570558734719247 35741311596855838102078871)
  ·
    refine ⟨53611967395283757153118307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35741311596855838102078871 53611967395283757153118307)
    ·
      refine ⟨80417951092925635729677461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53611967395283757153118307 80417951092925635729677461)
      ·
        refine ⟨3769591457480889174828631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80417951092925635729677461 3769591457480889174828631)
        ·
          refine ⟨5654387186221333762242947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3769591457480889174828631 5654387186221333762242947)
          ·
            refine ⟨8481580779332000643364421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5654387186221333762242947 8481580779332000643364421)
            ·
              refine ⟨1590296396124750120630829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8481580779332000643364421 1590296396124750120630829)
              ·
                refine ⟨596361148546781295236561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1590296396124750120630829 596361148546781295236561)
                ·
                  refine ⟨447270861410085971427421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596361148546781295236561 447270861410085971427421)
                  ·
                    rfl

theorem cell20_979939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 2].length) (baseStart_979939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979939 prefixEnd_979939 := by exact prefixLift 979939
  have htrace : WordTrace (prefixWord ++ tailWord_979939) baseStart_979939 baseEnd_979939 := by
    simpa [prefixWord, tailWord_979939, baseEnd_979939] using wordTrace_append hprefix tailTrace_979939
  have hstable : (prefixWord ++ tailWord_979939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979939).length < 2 ^ (prefixWord ++ tailWord_979939).sum := by decide
  have hdescent : baseEnd_979939 < baseStart_979939 := by decide
  rcases family_descends (prefixWord ++ tailWord_979939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979953 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 3]
def baseStart_979953 : Nat := 118140960795 + 979953 * 2 ^ 59
def prefixEnd_979953 : Nat := 4983230072969 + 3 ^ 40 * 979953 * 2
def baseEnd_979953 : Nat := 447277251391564144960697

theorem tailTrace_979953 : CollatzResearch.WordTrace tailWord_979953 prefixEnd_979953 447277251391564144960697 := by
  unfold tailWord_979953
  simp only [CollatzResearch.WordTrace]
  refine ⟨35741822218805118493088513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23827881479203412328725675 35741822218805118493088513)
  ·
    refine ⟨26806366664103838869816385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35741822218805118493088513 26806366664103838869816385)
    ·
      refine ⟨20104774998077879152362289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26806366664103838869816385 20104774998077879152362289)
      ·
        refine ⟨15078581248558409364271717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20104774998077879152362289 15078581248558409364271717)
        ·
          refine ⟨2827233984104701755800947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15078581248558409364271717 2827233984104701755800947)
          ·
            refine ⟨4240850976157052633701421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827233984104701755800947 4240850976157052633701421)
            ·
              refine ⟨1590319116058894737638033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4240850976157052633701421 1590319116058894737638033)
              ·
                refine ⟨1192739337044171053228525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590319116058894737638033 1192739337044171053228525)
                ·
                  refine ⟨447277251391564144960697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192739337044171053228525 447277251391564144960697)
                  ·
                    rfl

theorem cell20_979953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_979953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979953 prefixEnd_979953 := by exact prefixLift 979953
  have htrace : WordTrace (prefixWord ++ tailWord_979953) baseStart_979953 baseEnd_979953 := by
    simpa [prefixWord, tailWord_979953, baseEnd_979953] using wordTrace_append hprefix tailTrace_979953
  have hstable : (prefixWord ++ tailWord_979953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979953).length < 2 ^ (prefixWord ++ tailWord_979953).sum := by decide
  have hdescent : baseEnd_979953 < baseStart_979953 := by decide
  rcases family_descends (prefixWord ++ tailWord_979953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980012 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 3]
def baseStart_980012 : Nat := 118140960795 + 980012 * 2 ^ 59
def prefixEnd_980012 : Nat := 4983230072969 + 3 ^ 40 * 980012 * 2
def baseEnd_980012 : Nat := 447304180599222161993789

theorem tailTrace_980012 : CollatzResearch.WordTrace tailWord_980012 prefixEnd_980012 447304180599222161993789 := by
  unfold tailWord_980012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17871987062795685784743145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23829316083727581046324193 17871987062795685784743145)
  ·
    refine ⟨13403990297096764338557359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17871987062795685784743145 13403990297096764338557359)
    ·
      refine ⟨20105985445645146507836039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13403990297096764338557359 20105985445645146507836039)
      ·
        refine ⟨30158978168467719761754059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20105985445645146507836039 30158978168467719761754059)
        ·
          refine ⟨45238467252701579642631089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30158978168467719761754059 45238467252701579642631089)
          ·
            refine ⟨33928850439526184731973317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45238467252701579642631089 33928850439526184731973317)
            ·
              refine ⟨6361659457411159637244997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33928850439526184731973317 6361659457411159637244997)
              ·
                refine ⟨1192811148264592431983437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6361659457411159637244997 1192811148264592431983437)
                ·
                  refine ⟨447304180599222161993789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192811148264592431983437 447304180599222161993789)
                  ·
                    rfl

theorem cell20_980012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_980012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980012 prefixEnd_980012 := by exact prefixLift 980012
  have htrace : WordTrace (prefixWord ++ tailWord_980012) baseStart_980012 baseEnd_980012 := by
    simpa [prefixWord, tailWord_980012, baseEnd_980012] using wordTrace_append hprefix tailTrace_980012
  have hstable : (prefixWord ++ tailWord_980012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980012).length < 2 ^ (prefixWord ++ tailWord_980012).sum := by decide
  have hdescent : baseEnd_980012 < baseStart_980012 := by decide
  rcases family_descends (prefixWord ++ tailWord_980012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980022 : List Nat := [5, 1, 2, 1, 1, 3, 2, 5]
def baseStart_980022 : Nat := 118140960795 + 980022 * 2 ^ 59
def prefixEnd_980022 : Nat := 4983230072969 + 3 ^ 40 * 980022 * 2
def baseEnd_980022 : Nat := 149102914957235523886805

theorem tailTrace_980022 : CollatzResearch.WordTrace tailWord_980022 prefixEnd_980022 149102914957235523886805 := by
  unfold tailWord_980022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234021178472196454834395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23829559237036762184900213 2234021178472196454834395)
  ·
    refine ⟨3351031767708294682251593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2234021178472196454834395 3351031767708294682251593)
    ·
      refine ⟨2513273825781221011688695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3351031767708294682251593 2513273825781221011688695)
      ·
        refine ⟨3769910738671831517533043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513273825781221011688695 3769910738671831517533043)
        ·
          refine ⟨5654866108007747276299565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3769910738671831517533043 5654866108007747276299565)
          ·
            refine ⟨2120574790502905228612337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5654866108007747276299565 2120574790502905228612337)
            ·
              refine ⟨1590431092877178921459253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120574790502905228612337 1590431092877178921459253)
              ·
                refine ⟨149102914957235523886805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1590431092877178921459253 149102914957235523886805)
                ·
                  rfl

theorem cell20_980022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_980022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980022 prefixEnd_980022 := by exact prefixLift 980022
  have htrace : WordTrace (prefixWord ++ tailWord_980022) baseStart_980022 baseEnd_980022 := by
    simpa [prefixWord, tailWord_980022, baseEnd_980022] using wordTrace_append hprefix tailTrace_980022
  have hstable : (prefixWord ++ tailWord_980022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980022).length < 2 ^ (prefixWord ++ tailWord_980022).sum := by decide
  have hdescent : baseEnd_980022 < baseStart_980022 := by decide
  rcases family_descends (prefixWord ++ tailWord_980022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980026 : List Nat := [3, 1, 1, 1, 3, 1, 3, 7]
def baseStart_980026 : Nat := 118140960795 + 980026 * 2 ^ 59
def prefixEnd_980026 : Nat := 4983230072969 + 3 ^ 40 * 980026 * 2
def baseEnd_980026 : Nat := 149103523526900111842355

theorem tailTrace_980026 : CollatzResearch.WordTrace tailWord_980026 prefixEnd_980026 149103523526900111842355 := by
  unfold tailWord_980026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936121186885162990123983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23829656498360434640330621 8936121186885162990123983)
  ·
    refine ⟨13404181780327744485185975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8936121186885162990123983 13404181780327744485185975)
    ·
      refine ⟨20106272670491616727778963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13404181780327744485185975 20106272670491616727778963)
      ·
        refine ⟨30159409005737425091668445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20106272670491616727778963 30159409005737425091668445)
        ·
          refine ⟨11309778377151534409375667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30159409005737425091668445 11309778377151534409375667)
          ·
            refine ⟨16964667565727301614063501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11309778377151534409375667 16964667565727301614063501)
            ·
              refine ⟨6361750337147738105273813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16964667565727301614063501 6361750337147738105273813)
              ·
                refine ⟨149103523526900111842355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6361750337147738105273813 149103523526900111842355)
                ·
                  rfl

theorem cell20_980026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_980026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980026 prefixEnd_980026 := by exact prefixLift 980026
  have htrace : WordTrace (prefixWord ++ tailWord_980026) baseStart_980026 baseEnd_980026 := by
    simpa [prefixWord, tailWord_980026, baseEnd_980026] using wordTrace_append hprefix tailTrace_980026
  have hstable : (prefixWord ++ tailWord_980026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980026).length < 2 ^ (prefixWord ++ tailWord_980026).sum := by decide
  have hdescent : baseEnd_980026 < baseStart_980026 := by decide
  rcases family_descends (prefixWord ++ tailWord_980026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980029 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 3]
def baseStart_980029 : Nat := 118140960795 + 980029 * 2 ^ 59
def prefixEnd_980029 : Nat := 4983230072969 + 3 ^ 40 * 980029 * 2
def baseEnd_980029 : Nat := 447311939862445658427053

theorem tailTrace_980029 : CollatzResearch.WordTrace tailWord_980029 prefixEnd_980029 447311939862445658427053 := by
  unfold tailWord_980029
  simp only [CollatzResearch.WordTrace]
  refine ⟨35744594166529783472855141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23829729444353188981903427 35744594166529783472855141)
  ·
    refine ⟨6702111406224334401160339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35744594166529783472855141 6702111406224334401160339)
    ·
      refine ⟨10053167109336501601740509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702111406224334401160339 10053167109336501601740509)
      ·
        refine ⟨3769937666001188100652691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10053167109336501601740509 3769937666001188100652691)
        ·
          refine ⟨5654906499001782150979037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3769937666001188100652691 5654906499001782150979037)
          ·
            refine ⟨2120589937125668306617139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5654906499001782150979037 2120589937125668306617139)
            ·
              refine ⟨3180884905688502459925709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120589937125668306617139 3180884905688502459925709)
              ·
                refine ⟨1192831839633188422472141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3180884905688502459925709 1192831839633188422472141)
                ·
                  refine ⟨447311939862445658427053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192831839633188422472141 447311939862445658427053)
                  ·
                    rfl

theorem cell20_980029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_980029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980029 prefixEnd_980029 := by exact prefixLift 980029
  have htrace : WordTrace (prefixWord ++ tailWord_980029) baseStart_980029 baseEnd_980029 := by
    simpa [prefixWord, tailWord_980029, baseEnd_980029] using wordTrace_append hprefix tailTrace_980029
  have hstable : (prefixWord ++ tailWord_980029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980029).length < 2 ^ (prefixWord ++ tailWord_980029).sum := by decide
  have hdescent : baseEnd_980029 < baseStart_980029 := by decide
  rcases family_descends (prefixWord ++ tailWord_980029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980088 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 3]
def baseStart_980088 : Nat := 118140960795 + 980088 * 2 ^ 59
def prefixEnd_980088 : Nat := 4983230072969 + 3 ^ 40 * 980088 * 2
def baseEnd_980088 : Nat := 447338869070103675460145

theorem tailTrace_980088 : CollatzResearch.WordTrace tailWord_980088 prefixEnd_980088 447338869070103675460145 := by
  unfold tailWord_980088
  simp only [CollatzResearch.WordTrace]
  refine ⟨17873373036658018274626459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23831164048877357699501945 17873373036658018274626459)
  ·
    refine ⟨26810059554987027411939689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17873373036658018274626459 26810059554987027411939689)
    ·
      refine ⟨20107544666240270558954767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26810059554987027411939689 20107544666240270558954767)
      ·
        refine ⟨30161316999360405838432151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20107544666240270558954767 30161316999360405838432151)
        ·
          refine ⟨45241975499040608757648227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30161316999360405838432151 45241975499040608757648227)
          ·
            refine ⟨67862963248560913136472341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45241975499040608757648227 67862963248560913136472341)
            ·
              refine ⟨3181076402276292803272141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67862963248560913136472341 3181076402276292803272141)
              ·
                refine ⟨1192903650853609801227053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3181076402276292803272141 1192903650853609801227053)
                ·
                  refine ⟨447338869070103675460145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192903650853609801227053 447338869070103675460145)
                  ·
                    rfl

theorem cell20_980088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_980088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980088 prefixEnd_980088 := by exact prefixLift 980088
  have htrace : WordTrace (prefixWord ++ tailWord_980088) baseStart_980088 baseEnd_980088 := by
    simpa [prefixWord, tailWord_980088, baseEnd_980088] using wordTrace_append hprefix tailTrace_980088
  have hstable : (prefixWord ++ tailWord_980088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980088).length < 2 ^ (prefixWord ++ tailWord_980088).sum := by decide
  have hdescent : baseEnd_980088 < baseStart_980088 := by decide
  rcases family_descends (prefixWord ++ tailWord_980088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980122 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_980122 : Nat := 118140960795 + 980122 * 2 ^ 59
def prefixEnd_980122 : Nat := 4983230072969 + 3 ^ 40 * 980122 * 2
def baseEnd_980122 : Nat := 447354387596550668326673

theorem tailTrace_980122 : CollatzResearch.WordTrace tailWord_980122 prefixEnd_980122 447354387596550668326673 := by
  unfold tailWord_980122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936996538798215088997655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23831990770128573570660413 8936996538798215088997655)
  ·
    refine ⟨13405494808197322633496483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8936996538798215088997655 13405494808197322633496483)
    ·
      refine ⟨20108242212295983950244725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13405494808197322633496483 20108242212295983950244725)
      ·
        refine ⟨1885147707402748495335443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20108242212295983950244725 1885147707402748495335443)
        ·
          refine ⟨2827721561104122743003165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885147707402748495335443 2827721561104122743003165)
          ·
            refine ⟨1060395585414046028626187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2827721561104122743003165 1060395585414046028626187)
            ·
              refine ⟨1590593378121069042939281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060395585414046028626187 1590593378121069042939281)
              ·
                refine ⟨1192945033590801782204461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590593378121069042939281 1192945033590801782204461)
                ·
                  refine ⟨447354387596550668326673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192945033590801782204461 447354387596550668326673)
                  ·
                    rfl

theorem cell20_980122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_980122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980122 prefixEnd_980122 := by exact prefixLift 980122
  have htrace : WordTrace (prefixWord ++ tailWord_980122) baseStart_980122 baseEnd_980122 := by
    simpa [prefixWord, tailWord_980122, baseEnd_980122] using wordTrace_append hprefix tailTrace_980122
  have hstable : (prefixWord ++ tailWord_980122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980122).length < 2 ^ (prefixWord ++ tailWord_980122).sum := by decide
  have hdescent : baseEnd_980122 < baseStart_980122 := by decide
  rcases family_descends (prefixWord ++ tailWord_980122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980133 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_980133 : Nat := 118140960795 + 980133 * 2 ^ 59
def prefixEnd_980133 : Nat := 4983230072969 + 3 ^ 40 * 980133 * 2
def baseEnd_980133 : Nat := 447359408296283518959961

theorem tailTrace_980133 : CollatzResearch.WordTrace tailWord_980133 prefixEnd_980133 447359408296283518959961 := by
  unfold tailWord_980133
  simp only [CollatzResearch.WordTrace]
  refine ⟨35748387358153009234641053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23832258238768672823094035 35748387358153009234641053)
  ·
    refine ⟨13405645259307378462990395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35748387358153009234641053 13405645259307378462990395)
    ·
      refine ⟨20108467888961067694485593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13405645259307378462990395 20108467888961067694485593)
      ·
        refine ⟨15081350916720800770864195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20108467888961067694485593 15081350916720800770864195)
        ·
          refine ⟨22622026375081201156296293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15081350916720800770864195 22622026375081201156296293)
          ·
            refine ⟨4241629945327725216805555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22622026375081201156296293 4241629945327725216805555)
            ·
              refine ⟨6362444917991587825208333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241629945327725216805555 6362444917991587825208333)
              ·
                refine ⟨2385916844246845434453125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6362444917991587825208333 2385916844246845434453125)
                ·
                  refine ⟨447359408296283518959961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2385916844246845434453125 447359408296283518959961)
                  ·
                    rfl

theorem cell20_980133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_980133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980133 prefixEnd_980133 := by exact prefixLift 980133
  have htrace : WordTrace (prefixWord ++ tailWord_980133) baseStart_980133 baseEnd_980133 := by
    simpa [prefixWord, tailWord_980133, baseEnd_980133] using wordTrace_append hprefix tailTrace_980133
  have hstable : (prefixWord ++ tailWord_980133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980133).length < 2 ^ (prefixWord ++ tailWord_980133).sum := by decide
  have hdescent : baseEnd_980133 < baseStart_980133 := by decide
  rcases family_descends (prefixWord ++ tailWord_980133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980157 : List Nat := [1, 4, 1, 2, 1, 1, 6, 4]
def baseStart_980157 : Nat := 118140960795 + 980157 * 2 ^ 59
def prefixEnd_980157 : Nat := 4983230072969 + 3 ^ 40 * 980157 * 2
def baseEnd_980157 : Nat := 149123454183415367386621

theorem tailTrace_980157 : CollatzResearch.WordTrace tailWord_980157 prefixEnd_980157 149123454183415367386621 := by
  unfold tailWord_980157
  simp only [CollatzResearch.WordTrace]
  refine ⟨35749262710066061333514725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23832841806710707555676483 35749262710066061333514725)
  ·
    refine ⟨6702986758137386500034011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35749262710066061333514725 6702986758137386500034011)
    ·
      refine ⟨10054480137206079750051017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702986758137386500034011 10054480137206079750051017)
      ·
        refine ⟨7540860102904559812538263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10054480137206079750051017 7540860102904559812538263)
        ·
          refine ⟨11311290154356839718807395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7540860102904559812538263 11311290154356839718807395)
          ·
            refine ⟨16966935231535259578211093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311290154356839718807395 16966935231535259578211093)
            ·
              refine ⟨795325088978215292728645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16966935231535259578211093 795325088978215292728645)
              ·
                refine ⟨149123454183415367386621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 795325088978215292728645 149123454183415367386621)
                ·
                  rfl

theorem cell20_980157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 4].length) (baseStart_980157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980157 prefixEnd_980157 := by exact prefixLift 980157
  have htrace : WordTrace (prefixWord ++ tailWord_980157) baseStart_980157 baseEnd_980157 := by
    simpa [prefixWord, tailWord_980157, baseEnd_980157] using wordTrace_append hprefix tailTrace_980157
  have hstable : (prefixWord ++ tailWord_980157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980157).length < 2 ^ (prefixWord ++ tailWord_980157).sum := by decide
  have hdescent : baseEnd_980157 < baseStart_980157 := by decide
  rcases family_descends (prefixWord ++ tailWord_980157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980174 : List Nat := [4, 1, 1, 1, 6, 1, 6]
def baseStart_980174 : Nat := 118140960795 + 980174 * 2 ^ 59
def prefixEnd_980174 : Nat := 4983230072969 + 3 ^ 40 * 980174 * 2
def baseEnd_980174 : Nat := 49708680201496622065903

theorem tailTrace_980174 : CollatzResearch.WordTrace tailWord_980174 prefixEnd_980174 49708680201496622065903 := by
  unfold tailWord_980174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468735343875559154610447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23833255167336315491255717 4468735343875559154610447)
  ·
    refine ⟨6703103015813338731915671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4468735343875559154610447 6703103015813338731915671)
    ·
      refine ⟨10054654523720008097873507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6703103015813338731915671 10054654523720008097873507)
      ·
        refine ⟨15081981785580012146810261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10054654523720008097873507 15081981785580012146810261)
        ·
          refine ⟨706967896199063069381731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15081981785580012146810261 706967896199063069381731)
          ·
            refine ⟨1060451844298594604072597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706967896199063069381731 1060451844298594604072597)
            ·
              refine ⟨49708680201496622065903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1060451844298594604072597 49708680201496622065903)
              ·
                rfl

theorem cell20_980174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 6].length) (baseStart_980174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980174 prefixEnd_980174 := by exact prefixLift 980174
  have htrace : WordTrace (prefixWord ++ tailWord_980174) baseStart_980174 baseEnd_980174 := by
    simpa [prefixWord, tailWord_980174, baseEnd_980174] using wordTrace_append hprefix tailTrace_980174
  have hstable : (prefixWord ++ tailWord_980174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980174).length < 2 ^ (prefixWord ++ tailWord_980174).sum := by decide
  have hdescent : baseEnd_980174 < baseStart_980174 := by decide
  rcases family_descends (prefixWord ++ tailWord_980174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980184 : List Nat := [2, 1, 2, 2, 5, 1, 3, 2, 2]
def baseStart_980184 : Nat := 118140960795 + 980184 * 2 ^ 59
def prefixEnd_980184 : Nat := 4983230072969 + 3 ^ 40 * 980184 * 2
def baseEnd_980184 : Nat := 447382686085954008259753

theorem tailTrace_980184 : CollatzResearch.WordTrace tailWord_980184 prefixEnd_980184 447382686085954008259753 := by
  unfold tailWord_980184
  simp only [CollatzResearch.WordTrace]
  refine ⟨17875123740484122472373803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23833498320645496629831737 17875123740484122472373803)
  ·
    refine ⟨26812685610726183708560705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17875123740484122472373803 26812685610726183708560705)
    ·
      refine ⟨20109514208044637781420529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26812685610726183708560705 20109514208044637781420529)
      ·
        refine ⟨15082135656033478336065397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20109514208044637781420529 15082135656033478336065397)
        ·
          refine ⟨1413950217753138594006131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15082135656033478336065397 1413950217753138594006131)
          ·
            refine ⟨2120925326629707891009197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413950217753138594006131 2120925326629707891009197)
            ·
              refine ⟨795346997486140459128449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2120925326629707891009197 795346997486140459128449)
              ·
                refine ⟨596510248114605344346337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795346997486140459128449 596510248114605344346337)
                ·
                  refine ⟨447382686085954008259753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596510248114605344346337 447382686085954008259753)
                  ·
                    rfl

theorem cell20_980184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_980184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980184 prefixEnd_980184 := by exact prefixLift 980184
  have htrace : WordTrace (prefixWord ++ tailWord_980184) baseStart_980184 baseEnd_980184 := by
    simpa [prefixWord, tailWord_980184, baseEnd_980184] using wordTrace_append hprefix tailTrace_980184
  have hstable : (prefixWord ++ tailWord_980184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980184).length < 2 ^ (prefixWord ++ tailWord_980184).sum := by decide
  have hdescent : baseEnd_980184 < baseStart_980184 := by decide
  rcases family_descends (prefixWord ++ tailWord_980184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980247 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_980247 : Nat := 118140960795 + 980247 * 2 ^ 59
def prefixEnd_980247 : Nat := 4983230072969 + 3 ^ 40 * 980247 * 2
def baseEnd_980247 : Nat := 447411441002605789159495

theorem tailTrace_980247 : CollatzResearch.WordTrace tailWord_980247 prefixEnd_980247 447411441002605789159495 := by
  unfold tailWord_980247
  simp only [CollatzResearch.WordTrace]
  refine ⟨35752545279740006704290995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23835030186493337802860663 35752545279740006704290995)
  ·
    refine ⟨53628817919610010056436493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35752545279740006704290995 53628817919610010056436493)
    ·
      refine ⟨20110806719853753771163685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53628817919610010056436493 20110806719853753771163685)
      ·
        refine ⟨3770776259972578832093191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20110806719853753771163685 3770776259972578832093191)
        ·
          refine ⟨5656164389958868248139787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770776259972578832093191 5656164389958868248139787)
          ·
            refine ⟨8484246584938302372209681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5656164389958868248139787 8484246584938302372209681)
            ·
              refine ⟨6363184938703726779157261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8484246584938302372209681 6363184938703726779157261)
              ·
                refine ⟨2386194352013897542183973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6363184938703726779157261 2386194352013897542183973)
                ·
                  refine ⟨447411441002605789159495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386194352013897542183973 447411441002605789159495)
                  ·
                    rfl

theorem cell20_980247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_980247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980247 prefixEnd_980247 := by exact prefixLift 980247
  have htrace : WordTrace (prefixWord ++ tailWord_980247) baseStart_980247 baseEnd_980247 := by
    simpa [prefixWord, tailWord_980247, baseEnd_980247] using wordTrace_append hprefix tailTrace_980247
  have hstable : (prefixWord ++ tailWord_980247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980247).length < 2 ^ (prefixWord ++ tailWord_980247).sum := by decide
  have hdescent : baseEnd_980247 < baseStart_980247 := by decide
  rcases family_descends (prefixWord ++ tailWord_980247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980264 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_980264 : Nat := 118140960795 + 980264 * 2 ^ 59
def prefixEnd_980264 : Nat := 4983230072969 + 3 ^ 40 * 980264 * 2
def baseEnd_980264 : Nat := 447419200265829285592759

theorem tailTrace_980264 : CollatzResearch.WordTrace tailWord_980264 prefixEnd_980264 447419200265829285592759 := by
  unfold tailWord_980264
  simp only [CollatzResearch.WordTrace]
  refine ⟨17876582660339209303829923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23835443547118945738439897 17876582660339209303829923)
  ·
    refine ⟨26814873990508813955744885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17876582660339209303829923 26814873990508813955744885)
    ·
      refine ⟨2513894436610201308351083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26814873990508813955744885 2513894436610201308351083)
      ·
        refine ⟨3770841654915301962526625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513894436610201308351083 3770841654915301962526625)
        ·
          refine ⟨2828131241186476471894969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3770841654915301962526625 2828131241186476471894969)
          ·
            refine ⟨2121098430889857353921227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2828131241186476471894969 2121098430889857353921227)
            ·
              refine ⟨3181647646334786030881841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121098430889857353921227 3181647646334786030881841)
              ·
                refine ⟨2386235734751089523161381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3181647646334786030881841 2386235734751089523161381)
                ·
                  refine ⟨447419200265829285592759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386235734751089523161381 447419200265829285592759)
                  ·
                    rfl

theorem cell20_980264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_980264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980264 prefixEnd_980264 := by exact prefixLift 980264
  have htrace : WordTrace (prefixWord ++ tailWord_980264) baseStart_980264 baseEnd_980264 := by
    simpa [prefixWord, tailWord_980264, baseEnd_980264] using wordTrace_append hprefix tailTrace_980264
  have hstable : (prefixWord ++ tailWord_980264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980264).length < 2 ^ (prefixWord ++ tailWord_980264).sum := by decide
  have hdescent : baseEnd_980264 < baseStart_980264 := by decide
  rcases family_descends (prefixWord ++ tailWord_980264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980295 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 3]
def baseStart_980295 : Nat := 118140960795 + 980295 * 2 ^ 59
def prefixEnd_980295 : Nat := 4983230072969 + 3 ^ 40 * 980295 * 2
def baseEnd_980295 : Nat := 447433349510530955559299

theorem tailTrace_980295 : CollatzResearch.WordTrace tailWord_980295 prefixEnd_980295 447433349510530955559299 := by
  unfold tailWord_980295
  simp only [CollatzResearch.WordTrace]
  refine ⟨35754295983566110902038339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23836197322377407268025559 35754295983566110902038339)
  ·
    refine ⟨53631443975349166353057509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35754295983566110902038339 53631443975349166353057509)
    ·
      refine ⟨10055895745377968691198283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53631443975349166353057509 10055895745377968691198283)
      ·
        refine ⟨15083843618066953036797425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10055895745377968691198283 15083843618066953036797425)
        ·
          refine ⟨11312882713550214777598069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15083843618066953036797425 11312882713550214777598069)
          ·
            refine ⟨1060582754395332635399819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11312882713550214777598069 1060582754395332635399819)
            ·
              refine ⟨1590874131592998953099729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060582754395332635399819 1590874131592998953099729)
              ·
                refine ⟨1193155598694749214824797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590874131592998953099729 1193155598694749214824797)
                ·
                  refine ⟨447433349510530955559299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193155598694749214824797 447433349510530955559299)
                  ·
                    rfl

theorem cell20_980295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 3].length) (baseStart_980295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980295 prefixEnd_980295 := by exact prefixLift 980295
  have htrace : WordTrace (prefixWord ++ tailWord_980295) baseStart_980295 baseEnd_980295 := by
    simpa [prefixWord, tailWord_980295, baseEnd_980295] using wordTrace_append hprefix tailTrace_980295
  have hstable : (prefixWord ++ tailWord_980295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980295).length < 2 ^ (prefixWord ++ tailWord_980295).sum := by decide
  have hdescent : baseEnd_980295 < baseStart_980295 := by decide
  rcases family_descends (prefixWord ++ tailWord_980295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980302 : List Nat := [4, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_980302 : Nat := 118140960795 + 980302 * 2 ^ 59
def prefixEnd_980302 : Nat := 4983230072969 + 3 ^ 40 * 980302 * 2
def baseEnd_980302 : Nat := 447436544501270042325937

theorem tailTrace_980302 : CollatzResearch.WordTrace tailWord_980302 prefixEnd_980302 447436544501270042325937 := by
  unfold tailWord_980302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469318911817593887192895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23836367529693834065028773 4469318911817593887192895)
  ·
    refine ⟨6703978367726390830789343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4469318911817593887192895 6703978367726390830789343)
    ·
      refine ⟨10055967551589586246184015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6703978367726390830789343 10055967551589586246184015)
      ·
        refine ⟨15083951327384379369276023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10055967551589586246184015 15083951327384379369276023)
        ·
          refine ⟨22625926991076569053914035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15083951327384379369276023 22625926991076569053914035)
          ·
            refine ⟨33938890486614853580871053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22625926991076569053914035 33938890486614853580871053)
            ·
              refine ⟨12727083932480570092826645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33938890486614853580871053 12727083932480570092826645)
              ·
                refine ⟨596582059335026723101249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12727083932480570092826645 596582059335026723101249)
                ·
                  refine ⟨447436544501270042325937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596582059335026723101249 447436544501270042325937)
                  ·
                    rfl

theorem cell20_980302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_980302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980302 prefixEnd_980302 := by exact prefixLift 980302
  have htrace : WordTrace (prefixWord ++ tailWord_980302) baseStart_980302 baseEnd_980302 := by
    simpa [prefixWord, tailWord_980302, baseEnd_980302] using wordTrace_append hprefix tailTrace_980302
  have hstable : (prefixWord ++ tailWord_980302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980302).length < 2 ^ (prefixWord ++ tailWord_980302).sum := by decide
  have hdescent : baseEnd_980302 < baseStart_980302 := by decide
  rcases family_descends (prefixWord ++ tailWord_980302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980323 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_980323 : Nat := 118140960795 + 980323 * 2 ^ 59
def prefixEnd_980323 : Nat := 4983230072969 + 3 ^ 40 * 980323 * 2
def baseEnd_980323 : Nat := 447446129473487302625851

theorem tailTrace_980323 : CollatzResearch.WordTrace tailWord_980323 prefixEnd_980323 447446129473487302625851 := by
  unfold tailWord_980323
  simp only [CollatzResearch.WordTrace]
  refine ⟨35755317227464671684057623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23836878151643114456038415 35755317227464671684057623)
  ·
    refine ⟨53632975841197007526086435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35755317227464671684057623 53632975841197007526086435)
    ·
      refine ⟨80449463761795511289129653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53632975841197007526086435 80449463761795511289129653)
      ·
        refine ⟨7542137227668329183355905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80449463761795511289129653 7542137227668329183355905)
        ·
          refine ⟨5656602920751246887516929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7542137227668329183355905 5656602920751246887516929)
          ·
            refine ⟨4242452190563435165637697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5656602920751246887516929 4242452190563435165637697)
            ·
              refine ⟨3181839142922576374228273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4242452190563435165637697 3181839142922576374228273)
              ·
                refine ⟨2386379357191932280671205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3181839142922576374228273 2386379357191932280671205)
                ·
                  refine ⟨447446129473487302625851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386379357191932280671205 447446129473487302625851)
                  ·
                    rfl

theorem cell20_980323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_980323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980323 prefixEnd_980323 := by exact prefixLift 980323
  have htrace : WordTrace (prefixWord ++ tailWord_980323) baseStart_980323 baseEnd_980323 := by
    simpa [prefixWord, tailWord_980323, baseEnd_980323] using wordTrace_append hprefix tailTrace_980323
  have hstable : (prefixWord ++ tailWord_980323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980323).length < 2 ^ (prefixWord ++ tailWord_980323).sum := by decide
  have hdescent : baseEnd_980323 < baseStart_980323 := by decide
  rcases family_descends (prefixWord ++ tailWord_980323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980337 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_980337 : Nat := 118140960795 + 980337 * 2 ^ 59
def prefixEnd_980337 : Nat := 4983230072969 + 3 ^ 40 * 980337 * 2
def baseEnd_980337 : Nat := 447452519454965476159127

theorem tailTrace_980337 : CollatzResearch.WordTrace tailWord_980337 prefixEnd_980337 447452519454965476159127 := by
  unfold tailWord_980337
  simp only [CollatzResearch.WordTrace]
  refine ⟨35755827849413952075067265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23837218566275968050044843 35755827849413952075067265)
  ·
    refine ⟨26816870887060464056300449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35755827849413952075067265 26816870887060464056300449)
    ·
      refine ⟨20112653165295348042225337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26816870887060464056300449 20112653165295348042225337)
      ·
        refine ⟨15084489873971511031669003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20112653165295348042225337 15084489873971511031669003)
        ·
          refine ⟨22626734810957266547503505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15084489873971511031669003 22626734810957266547503505)
          ·
            refine ⟨16970051108217949910627629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22626734810957266547503505 16970051108217949910627629)
            ·
              refine ⟨6363769165581731216485361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16970051108217949910627629 6363769165581731216485361)
              ·
                refine ⟨4772826874186298412364021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6363769165581731216485361 4772826874186298412364021)
                ·
                  refine ⟨447452519454965476159127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4772826874186298412364021 447452519454965476159127)
                  ·
                    rfl

theorem cell20_980337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_980337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980337 prefixEnd_980337 := by exact prefixLift 980337
  have htrace : WordTrace (prefixWord ++ tailWord_980337) baseStart_980337 baseEnd_980337 := by
    simpa [prefixWord, tailWord_980337, baseEnd_980337] using wordTrace_append hprefix tailTrace_980337
  have hstable : (prefixWord ++ tailWord_980337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980337).length < 2 ^ (prefixWord ++ tailWord_980337).sum := by decide
  have hdescent : baseEnd_980337 < baseStart_980337 := by decide
  rcases family_descends (prefixWord ++ tailWord_980337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980409 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 3]
def baseStart_980409 : Nat := 118140960795 + 980409 * 2 ^ 59
def prefixEnd_980409 : Nat := 4983230072969 + 3 ^ 40 * 980409 * 2
def baseEnd_980409 : Nat := 447485382216853225758833

theorem tailTrace_980409 : CollatzResearch.WordTrace tailWord_980409 prefixEnd_980409 447485382216853225758833 := by
  unfold tailWord_980409
  simp only [CollatzResearch.WordTrace]
  refine ⟨35758453905153108371688281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23838969270102072247792187 35758453905153108371688281)
  ·
    refine ⟨26818840428864831278766211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35758453905153108371688281 26818840428864831278766211)
    ·
      refine ⟨40228260643297246918149317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26818840428864831278766211 40228260643297246918149317)
      ·
        refine ⟨7542798870618233797152997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40228260643297246918149317 7542798870618233797152997)
        ·
          refine ⟨1414274788240918836966187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7542798870618233797152997 1414274788240918836966187)
          ·
            refine ⟨2121412182361378255449281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414274788240918836966187 2121412182361378255449281)
            ·
              refine ⟨1591059136771033691586961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2121412182361378255449281 1591059136771033691586961)
              ·
                refine ⟨1193294352578275268690221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1591059136771033691586961 1193294352578275268690221)
                ·
                  refine ⟨447485382216853225758833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193294352578275268690221 447485382216853225758833)
                  ·
                    rfl

theorem cell20_980409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_980409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980409 prefixEnd_980409 := by exact prefixLift 980409
  have htrace : WordTrace (prefixWord ++ tailWord_980409) baseStart_980409 baseEnd_980409 := by
    simpa [prefixWord, tailWord_980409, baseEnd_980409] using wordTrace_append hprefix tailTrace_980409
  have hstable : (prefixWord ++ tailWord_980409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980409).length < 2 ^ (prefixWord ++ tailWord_980409).sum := by decide
  have hdescent : baseEnd_980409 < baseStart_980409 := by decide
  rcases family_descends (prefixWord ++ tailWord_980409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980430 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_980430 : Nat := 118140960795 + 980430 * 2 ^ 59
def prefixEnd_980430 : Nat := 4983230072969 + 3 ^ 40 * 980430 * 2
def baseEnd_980430 : Nat := 447494967189070486058747

theorem tailTrace_980430 : CollatzResearch.WordTrace tailWord_980430 prefixEnd_980430 447494967189070486058747 := by
  unfold tailWord_980430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469902479759628619775343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23839479892051352638801829 4469902479759628619775343)
  ·
    refine ⟨6704853719639442929663015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4469902479759628619775343 6704853719639442929663015)
    ·
      refine ⟨10057280579459164394494523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6704853719639442929663015 10057280579459164394494523)
      ·
        refine ⟨15085920869188746591741785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057280579459164394494523 15085920869188746591741785)
        ·
          refine ⟨11314440651891559943806339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15085920869188746591741785 11314440651891559943806339)
          ·
            refine ⟨16971660977837339915709509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11314440651891559943806339 16971660977837339915709509)
            ·
              refine ⟨3182186433344501234195533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16971660977837339915709509 3182186433344501234195533)
              ·
                refine ⟨1193319912504187962823325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3182186433344501234195533 1193319912504187962823325)
                ·
                  refine ⟨447494967189070486058747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193319912504187962823325 447494967189070486058747)
                  ·
                    rfl

theorem cell20_980430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_980430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980430 prefixEnd_980430 := by exact prefixLift 980430
  have htrace : WordTrace (prefixWord ++ tailWord_980430) baseStart_980430 baseEnd_980430 := by
    simpa [prefixWord, tailWord_980430, baseEnd_980430] using wordTrace_append hprefix tailTrace_980430
  have hstable : (prefixWord ++ tailWord_980430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980430).length < 2 ^ (prefixWord ++ tailWord_980430).sum := by decide
  have hdescent : baseEnd_980430 < baseStart_980430 := by decide
  rcases family_descends (prefixWord ++ tailWord_980430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980437 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_980437 : Nat := 118140960795 + 980437 * 2 ^ 59
def prefixEnd_980437 : Nat := 4983230072969 + 3 ^ 40 * 980437 * 2
def baseEnd_980437 : Nat := 447498162179809572825385

theorem tailTrace_980437 : CollatzResearch.WordTrace tailWord_980437 prefixEnd_980437 447498162179809572825385 := by
  unfold tailWord_980437
  simp only [CollatzResearch.WordTrace]
  refine ⟨35759475149051669153707565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23839650099367779435805043 35759475149051669153707565)
  ·
    refine ⟨13409803180894375932640337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35759475149051669153707565 13409803180894375932640337)
    ·
      refine ⟨10057352385670781949480253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13409803180894375932640337 10057352385670781949480253)
      ·
        refine ⟨3771507144626543231055095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10057352385670781949480253 3771507144626543231055095)
        ·
          refine ⟨5657260716939814846582643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771507144626543231055095 5657260716939814846582643)
          ·
            refine ⟨8485891075409722269873965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5657260716939814846582643 8485891075409722269873965)
            ·
              refine ⟨3182209153278645851202737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8485891075409722269873965 3182209153278645851202737)
              ·
                refine ⟨2386656864958984388402053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182209153278645851202737 2386656864958984388402053)
                ·
                  refine ⟨447498162179809572825385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386656864958984388402053 447498162179809572825385)
                  ·
                    rfl

theorem cell20_980437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_980437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980437 prefixEnd_980437 := by exact prefixLift 980437
  have htrace : WordTrace (prefixWord ++ tailWord_980437) baseStart_980437 baseEnd_980437 := by
    simpa [prefixWord, tailWord_980437, baseEnd_980437] using wordTrace_append hprefix tailTrace_980437
  have hstable : (prefixWord ++ tailWord_980437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980437).length < 2 ^ (prefixWord ++ tailWord_980437).sum := by decide
  have hdescent : baseEnd_980437 < baseStart_980437 := by decide
  rcases family_descends (prefixWord ++ tailWord_980437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980461 : List Nat := [1, 5, 1, 3, 2, 1, 7]
def baseStart_980461 : Nat := 118140960795 + 980461 * 2 ^ 59
def prefixEnd_980461 : Nat := 4983230072969 + 3 ^ 40 * 980461 * 2
def baseEnd_980461 : Nat := 49723235159308017336143

theorem tailTrace_980461 : CollatzResearch.WordTrace tailWord_980461 prefixEnd_980461 49723235159308017336143 := by
  unfold tailWord_980461
  simp only [CollatzResearch.WordTrace]
  refine ⟨35760350500964721252581237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23840233667309814168387491 35760350500964721252581237)
  ·
    refine ⟨3352532859465442617429491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35760350500964721252581237 3352532859465442617429491)
    ·
      refine ⟨5028799289198163926144237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3352532859465442617429491 5028799289198163926144237)
      ·
        refine ⟨1885799733449311472304089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5028799289198163926144237 1885799733449311472304089)
        ·
          refine ⟨1414349800086983604228067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885799733449311472304089 1414349800086983604228067)
          ·
            refine ⟨2121524700130475406342101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414349800086983604228067 2121524700130475406342101)
            ·
              refine ⟨49723235159308017336143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2121524700130475406342101 49723235159308017336143)
              ·
                rfl

theorem cell20_980461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 7].length) (baseStart_980461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980461 prefixEnd_980461 := by exact prefixLift 980461
  have htrace : WordTrace (prefixWord ++ tailWord_980461) baseStart_980461 baseEnd_980461 := by
    simpa [prefixWord, tailWord_980461, baseEnd_980461] using wordTrace_append hprefix tailTrace_980461
  have hstable : (prefixWord ++ tailWord_980461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980461).length < 2 ^ (prefixWord ++ tailWord_980461).sum := by decide
  have hdescent : baseEnd_980461 < baseStart_980461 := by decide
  rcases family_descends (prefixWord ++ tailWord_980461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980499 : List Nat := [1, 1, 1, 2, 1, 8, 2, 4]
def baseStart_980499 : Nat := 118140960795 + 980499 * 2 ^ 59
def prefixEnd_980499 : Nat := 4983230072969 + 3 ^ 40 * 980499 * 2
def baseEnd_980499 : Nat := 149175486889737637586155

theorem tailTrace_980499 : CollatzResearch.WordTrace tailWord_980499 prefixEnd_980499 149175486889737637586155 := by
  unfold tailWord_980499
  simp only [CollatzResearch.WordTrace]
  refine ⟨35761736474827053742464551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23841157649884702494976367 35761736474827053742464551)
  ·
    refine ⟨53642604712240580613696827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35761736474827053742464551 53642604712240580613696827)
    ·
      refine ⟨80463907068360870920545241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53642604712240580613696827 80463907068360870920545241)
      ·
        refine ⟨60347930301270653190408931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80463907068360870920545241 60347930301270653190408931)
        ·
          refine ⟨90521895451905979785613397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60347930301270653190408931 90521895451905979785613397)
          ·
            refine ⟨1060803462327023200612657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 90521895451905979785613397 1060803462327023200612657)
            ·
              refine ⟨795602596745267400459493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060803462327023200612657 795602596745267400459493)
              ·
                refine ⟨149175486889737637586155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 795602596745267400459493 149175486889737637586155)
                ·
                  rfl

theorem cell20_980499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 4].length) (baseStart_980499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980499 prefixEnd_980499 := by exact prefixLift 980499
  have htrace : WordTrace (prefixWord ++ tailWord_980499) baseStart_980499 baseEnd_980499 := by
    simpa [prefixWord, tailWord_980499, baseEnd_980499] using wordTrace_append hprefix tailTrace_980499
  have hstable : (prefixWord ++ tailWord_980499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980499).length < 2 ^ (prefixWord ++ tailWord_980499).sum := by decide
  have hdescent : baseEnd_980499 < baseStart_980499 := by decide
  rcases family_descends (prefixWord ++ tailWord_980499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980526 : List Nat := [4, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_980526 : Nat := 118140960795 + 980526 * 2 ^ 59
def prefixEnd_980526 : Nat := 4983230072969 + 3 ^ 40 * 980526 * 2
def baseEnd_980526 : Nat := 447538784204920818858355

theorem tailTrace_980526 : CollatzResearch.WordTrace tailWord_980526 prefixEnd_980526 447538784204920818858355 := by
  unfold tailWord_980526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470340155716154669212179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23841814163819491569131621 4470340155716154669212179)
  ·
    refine ⟨6705510233574232003818269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4470340155716154669212179 6705510233574232003818269)
    ·
      refine ⟨2514566337590337001431851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6705510233574232003818269 2514566337590337001431851)
      ·
        refine ⟨3771849506385505502147777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2514566337590337001431851 3771849506385505502147777)
        ·
          refine ⟨2828887129789129126610833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3771849506385505502147777 2828887129789129126610833)
          ·
            refine ⟨2121665347341846844958125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2828887129789129126610833 2121665347341846844958125)
            ·
              refine ⟨795624505253192566859297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2121665347341846844958125 795624505253192566859297)
              ·
                refine ⟨596718378939894425144473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795624505253192566859297 596718378939894425144473)
                ·
                  refine ⟨447538784204920818858355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596718378939894425144473 447538784204920818858355)
                  ·
                    rfl

theorem cell20_980526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_980526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980526 prefixEnd_980526 := by exact prefixLift 980526
  have htrace : WordTrace (prefixWord ++ tailWord_980526) baseStart_980526 baseEnd_980526 := by
    simpa [prefixWord, tailWord_980526, baseEnd_980526] using wordTrace_append hprefix tailTrace_980526
  have hstable : (prefixWord ++ tailWord_980526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980526).length < 2 ^ (prefixWord ++ tailWord_980526).sum := by decide
  have hdescent : baseEnd_980526 < baseStart_980526 := by decide
  rcases family_descends (prefixWord ++ tailWord_980526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980540 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 3]
def baseStart_980540 : Nat := 118140960795 + 980540 * 2 ^ 59
def prefixEnd_980540 : Nat := 4983230072969 + 3 ^ 40 * 980540 * 2
def baseEnd_980540 : Nat := 447545174186398992391631

theorem tailTrace_980540 : CollatzResearch.WordTrace tailWord_980540 prefixEnd_980540 447545174186398992391631 := by
  unfold tailWord_980540
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881615933839258872353537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23842154578452345163138049 17881615933839258872353537)
  ·
    refine ⟨13411211950379444154265153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17881615933839258872353537 13411211950379444154265153)
    ·
      refine ⟨10058408962784583115698865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13411211950379444154265153 10058408962784583115698865)
      ·
        refine ⟨7543806722088437336774149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10058408962784583115698865 7543806722088437336774149)
        ·
          refine ⟨1414463760391582000645153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7543806722088437336774149 1414463760391582000645153)
          ·
            refine ⟨1060847820293686500483865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414463760391582000645153 1060847820293686500483865)
            ·
              refine ⟨795635865220264875362899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060847820293686500483865 795635865220264875362899)
              ·
                refine ⟨1193453797830397313044349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795635865220264875362899 1193453797830397313044349)
                ·
                  refine ⟨447545174186398992391631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193453797830397313044349 447545174186398992391631)
                  ·
                    rfl

theorem cell20_980540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_980540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980540 prefixEnd_980540 := by exact prefixLift 980540
  have htrace : WordTrace (prefixWord ++ tailWord_980540) baseStart_980540 baseEnd_980540 := by
    simpa [prefixWord, tailWord_980540, baseEnd_980540] using wordTrace_append hprefix tailTrace_980540
  have hstable : (prefixWord ++ tailWord_980540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980540).length < 2 ^ (prefixWord ++ tailWord_980540).sum := by decide
  have hdescent : baseEnd_980540 < baseStart_980540 := by decide
  rcases family_descends (prefixWord ++ tailWord_980540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980579 : List Nat := [1, 1, 1, 5, 1, 11]
def baseStart_980579 : Nat := 118140960795 + 980579 * 2 ^ 59
def prefixEnd_980579 : Nat := 4983230072969 + 3 ^ 40 * 980579 * 2
def baseEnd_980579 : Nat := 16576406475892155188573

theorem tailTrace_980579 : CollatzResearch.WordTrace tailWord_980579 prefixEnd_980579 16576406475892155188573 := by
  unfold tailWord_980579
  simp only [CollatzResearch.WordTrace]
  refine ⟨35764654314537227405376791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23843102876358151603584527 35764654314537227405376791)
  ·
    refine ⟨53646981471805841108065187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35764654314537227405376791 53646981471805841108065187)
    ·
      refine ⟨80470472207708761662097781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53646981471805841108065187 80470472207708761662097781)
      ·
        refine ⟨7544106769472696405821667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80470472207708761662097781 7544106769472696405821667)
        ·
          refine ⟨11316160154209044608732501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544106769472696405821667 11316160154209044608732501)
          ·
            refine ⟨16576406475892155188573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11316160154209044608732501 16576406475892155188573)
            ·
              rfl

theorem cell20_980579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 11].length) (baseStart_980579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980579 prefixEnd_980579 := by exact prefixLift 980579
  have htrace : WordTrace (prefixWord ++ tailWord_980579) baseStart_980579 baseEnd_980579 := by
    simpa [prefixWord, tailWord_980579, baseEnd_980579] using wordTrace_append hprefix tailTrace_980579
  have hstable : (prefixWord ++ tailWord_980579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980579).length < 2 ^ (prefixWord ++ tailWord_980579).sum := by decide
  have hdescent : baseEnd_980579 < baseStart_980579 := by decide
  rcases family_descends (prefixWord ++ tailWord_980579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980603 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 3]
def baseStart_980603 : Nat := 118140960795 + 980603 * 2 ^ 59
def prefixEnd_980603 : Nat := 4983230072969 + 3 ^ 40 * 980603 * 2
def baseEnd_980603 : Nat := 447573929103050773291373

theorem tailTrace_980603 : CollatzResearch.WordTrace tailWord_980603 prefixEnd_980603 447573929103050773291373 := by
  unfold tailWord_980603
  simp only [CollatzResearch.WordTrace]
  refine ⟨35765529666450279504250463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23843686444300186336166975 35765529666450279504250463)
  ·
    refine ⟨53648294499675419256375695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35765529666450279504250463 53648294499675419256375695)
    ·
      refine ⟨80472441749513128884563543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53648294499675419256375695 80472441749513128884563543)
      ·
        refine ⟨120708662624269693326845315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80472441749513128884563543 120708662624269693326845315)
        ·
          refine ⟨181062993936404539990267973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120708662624269693326845315 181062993936404539990267973)
          ·
            refine ⟨33949311363075851248175245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181062993936404539990267973 33949311363075851248175245)
            ·
              refine ⟨12730991761153444218065717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33949311363075851248175245 12730991761153444218065717)
              ·
                refine ⟨1193530477608135395443661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12730991761153444218065717 1193530477608135395443661)
                ·
                  refine ⟨447573929103050773291373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193530477608135395443661 447573929103050773291373)
                  ·
                    rfl

theorem cell20_980603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 3].length) (baseStart_980603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980603 prefixEnd_980603 := by exact prefixLift 980603
  have htrace : WordTrace (prefixWord ++ tailWord_980603) baseStart_980603 baseEnd_980603 := by
    simpa [prefixWord, tailWord_980603, baseEnd_980603] using wordTrace_append hprefix tailTrace_980603
  have hstable : (prefixWord ++ tailWord_980603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980603).length < 2 ^ (prefixWord ++ tailWord_980603).sum := by decide
  have hdescent : baseEnd_980603 < baseStart_980603 := by decide
  rcases family_descends (prefixWord ++ tailWord_980603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980617 : List Nat := [1, 2, 1, 1, 4, 1, 2, 8]
def baseStart_980617 : Nat := 118140960795 + 980617 * 2 ^ 59
def prefixEnd_980617 : Nat := 4983230072969 + 3 ^ 40 * 980617 * 2
def baseEnd_980617 : Nat := 149193439694842982274883

theorem tailTrace_980617 : CollatzResearch.WordTrace tailWord_980617 prefixEnd_980617 149193439694842982274883 := by
  unfold tailWord_980617
  simp only [CollatzResearch.WordTrace]
  refine ⟨35766040288399559895260105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23844026858933039930173403 35766040288399559895260105)
  ·
    refine ⟨26824530216299669921445079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35766040288399559895260105 26824530216299669921445079)
    ·
      refine ⟨40236795324449504882167619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26824530216299669921445079 40236795324449504882167619)
      ·
        refine ⟨60355192986674257323251429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40236795324449504882167619 60355192986674257323251429)
        ·
          refine ⟨11316598685001423248109643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60355192986674257323251429 11316598685001423248109643)
          ·
            refine ⟨16974898027502134872164465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11316598685001423248109643 16974898027502134872164465)
            ·
              refine ⟨12731173520626601154123349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16974898027502134872164465 12731173520626601154123349)
              ·
                refine ⟨149193439694842982274883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12731173520626601154123349 149193439694842982274883)
                ·
                  rfl

theorem cell20_980617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_980617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980617 prefixEnd_980617 := by exact prefixLift 980617
  have htrace : WordTrace (prefixWord ++ tailWord_980617) baseStart_980617 baseEnd_980617 := by
    simpa [prefixWord, tailWord_980617, baseEnd_980617] using wordTrace_append hprefix tailTrace_980617
  have hstable : (prefixWord ++ tailWord_980617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980617).length < 2 ^ (prefixWord ++ tailWord_980617).sum := by decide
  have hdescent : baseEnd_980617 < baseStart_980617 := by decide
  rcases family_descends (prefixWord ++ tailWord_980617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980644 : List Nat := [2, 3, 1, 2, 2, 2, 2, 4, 2]
def baseStart_980644 : Nat := 118140960795 + 980644 * 2 ^ 59
def prefixEnd_980644 : Nat := 4983230072969 + 3 ^ 40 * 980644 * 2
def baseEnd_980644 : Nat := 447592642620236852924539

theorem tailTrace_980644 : CollatzResearch.WordTrace tailWord_980644 prefixEnd_980644 447592642620236852924539 := by
  unfold tailWord_980644
  simp only [CollatzResearch.WordTrace]
  refine ⟨17883512529650871753246493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23844683372867829004328657 17883512529650871753246493)
  ·
    refine ⟨6706317198619076907467435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17883512529650871753246493 6706317198619076907467435)
    ·
      refine ⟨10059475797928615361201153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6706317198619076907467435 10059475797928615361201153)
      ·
        refine ⟨7544606848446461520900865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10059475797928615361201153 7544606848446461520900865)
        ·
          refine ⟨5658455136334846140675649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7544606848446461520900865 5658455136334846140675649)
          ·
            refine ⟨4243841352251134605506737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5658455136334846140675649 4243841352251134605506737)
            ·
              refine ⟨3182881014188350954130053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4243841352251134605506737 3182881014188350954130053)
              ·
                refine ⟨596790190160315803899385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3182881014188350954130053 596790190160315803899385)
                ·
                  refine ⟨447592642620236852924539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596790190160315803899385 447592642620236852924539)
                  ·
                    rfl

theorem cell20_980644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_980644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980644 prefixEnd_980644 := by exact prefixLift 980644
  have htrace : WordTrace (prefixWord ++ tailWord_980644) baseStart_980644 baseEnd_980644 := by
    simpa [prefixWord, tailWord_980644, baseEnd_980644] using wordTrace_append hprefix tailTrace_980644
  have hstable : (prefixWord ++ tailWord_980644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980644).length < 2 ^ (prefixWord ++ tailWord_980644).sum := by decide
  have hdescent : baseEnd_980644 < baseStart_980644 := by decide
  rcases family_descends (prefixWord ++ tailWord_980644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980655 : List Nat := [1, 1, 2, 1, 2, 4, 2, 7]
def baseStart_980655 : Nat := 118140960795 + 980655 * 2 ^ 59
def prefixEnd_980655 : Nat := 4983230072969 + 3 ^ 40 * 980655 * 2
def baseEnd_980655 : Nat := 149199221106656567852609

theorem tailTrace_980655 : CollatzResearch.WordTrace tailWord_980655 prefixEnd_980655 149199221106656567852609 := by
  unfold tailWord_980655
  simp only [CollatzResearch.WordTrace]
  refine ⟨35767426262261892385143419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23844950841507928256762279 35767426262261892385143419)
  ·
    refine ⟨53651139393392838577715129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35767426262261892385143419 53651139393392838577715129)
    ·
      refine ⟨40238354545044628933286347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53651139393392838577715129 40238354545044628933286347)
      ·
        refine ⟨60357531817566943399929521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40238354545044628933286347 60357531817566943399929521)
        ·
          refine ⟨45268148863175207549947141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60357531817566943399929521 45268148863175207549947141)
          ·
            refine ⟨8487777911845351415615089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45268148863175207549947141 8487777911845351415615089)
            ·
              refine ⟨6365833433884013561711317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8487777911845351415615089 6365833433884013561711317)
              ·
                refine ⟨149199221106656567852609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6365833433884013561711317 149199221106656567852609)
                ·
                  rfl

theorem cell20_980655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_980655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980655 prefixEnd_980655 := by exact prefixLift 980655
  have htrace : WordTrace (prefixWord ++ tailWord_980655) baseStart_980655 baseEnd_980655 := by
    simpa [prefixWord, tailWord_980655, baseEnd_980655] using wordTrace_append hprefix tailTrace_980655
  have hstable : (prefixWord ++ tailWord_980655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980655).length < 2 ^ (prefixWord ++ tailWord_980655).sum := by decide
  have hdescent : baseEnd_980655 < baseStart_980655 := by decide
  rcases family_descends (prefixWord ++ tailWord_980655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980674 : List Nat := [3, 5, 1, 2, 1, 2, 1, 3, 2]
def baseStart_980674 : Nat := 118140960795 + 980674 * 2 ^ 59
def prefixEnd_980674 : Nat := 4983230072969 + 3 ^ 40 * 980674 * 2
def baseEnd_980674 : Nat := 447606335437690081924417

theorem tailTrace_980674 : CollatzResearch.WordTrace tailWord_980674 prefixEnd_980674 447606335437690081924417 := by
  unfold tailWord_980674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8942029812298264657521269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23845412832795372420056717 8942029812298264657521269)
  ·
    refine ⟨838315294902962311642619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8942029812298264657521269 838315294902962311642619)
    ·
      refine ⟨1257472942354443467463929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838315294902962311642619 1257472942354443467463929)
      ·
        refine ⟨943104706765832600597947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1257472942354443467463929 943104706765832600597947)
        ·
          refine ⟨1414657060148748900896921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943104706765832600597947 1414657060148748900896921)
          ·
            refine ⟨1060992795111561675672691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414657060148748900896921 1060992795111561675672691)
            ·
              refine ⟨1591489192667342513509037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060992795111561675672691 1591489192667342513509037)
              ·
                refine ⟨596808447250253442565889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1591489192667342513509037 596808447250253442565889)
                ·
                  refine ⟨447606335437690081924417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596808447250253442565889 447606335437690081924417)
                  ·
                    rfl

theorem cell20_980674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_980674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980674 prefixEnd_980674 := by exact prefixLift 980674
  have htrace : WordTrace (prefixWord ++ tailWord_980674) baseStart_980674 baseEnd_980674 := by
    simpa [prefixWord, tailWord_980674, baseEnd_980674] using wordTrace_append hprefix tailTrace_980674
  have hstable : (prefixWord ++ tailWord_980674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980674).length < 2 ^ (prefixWord ++ tailWord_980674).sum := by decide
  have hdescent : baseEnd_980674 < baseStart_980674 := by decide
  rcases family_descends (prefixWord ++ tailWord_980674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980754 : List Nat := [3, 2, 4, 1, 1, 1, 4, 2, 2]
def baseStart_980754 : Nat := 118140960795 + 980754 * 2 ^ 59
def prefixEnd_980754 : Nat := 4983230072969 + 3 ^ 40 * 980754 * 2
def baseEnd_980754 : Nat := 447642849617565359257423

theorem tailTrace_980754 : CollatzResearch.WordTrace tailWord_980754 prefixEnd_980754 447642849617565359257423 := by
  unfold tailWord_980754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8942759272225808073249329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23847358059268821528664877 8942759272225808073249329)
  ·
    refine ⟨6707069454169356054936997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8942759272225808073249329 6707069454169356054936997)
    ·
      refine ⟨1257575522656754260300687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6707069454169356054936997 1257575522656754260300687)
      ·
        refine ⟨1886363283985131390451031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257575522656754260300687 1886363283985131390451031)
        ·
          refine ⟨2829544925977697085676547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886363283985131390451031 2829544925977697085676547)
          ·
            refine ⟨4244317388966545628514821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829544925977697085676547 4244317388966545628514821)
            ·
              refine ⟨795809510431227305346529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4244317388966545628514821 795809510431227305346529)
              ·
                refine ⟨596857132823420479009897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795809510431227305346529 596857132823420479009897)
                ·
                  refine ⟨447642849617565359257423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596857132823420479009897 447642849617565359257423)
                  ·
                    rfl

theorem cell20_980754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_980754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980754 prefixEnd_980754 := by exact prefixLift 980754
  have htrace : WordTrace (prefixWord ++ tailWord_980754) baseStart_980754 baseEnd_980754 := by
    simpa [prefixWord, tailWord_980754, baseEnd_980754] using wordTrace_append hprefix tailTrace_980754
  have hstable : (prefixWord ++ tailWord_980754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980754).length < 2 ^ (prefixWord ++ tailWord_980754).sum := by decide
  have hdescent : baseEnd_980754 < baseStart_980754 := by decide
  rcases family_descends (prefixWord ++ tailWord_980754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980772 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 3]
def baseStart_980772 : Nat := 118140960795 + 980772 * 2 ^ 59
def prefixEnd_980772 : Nat := 4983230072969 + 3 ^ 40 * 980772 * 2
def baseEnd_980772 : Nat := 447651065308037296657349

theorem tailTrace_980772 : CollatzResearch.WordTrace tailWord_980772 prefixEnd_980772 447651065308037296657349 := by
  unfold tailWord_980772
  simp only [CollatzResearch.WordTrace]
  refine ⟨17885846801419010683576285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23847795735225347578101713 17885846801419010683576285)
  ·
    refine ⟨6707192550532129006341107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17885846801419010683576285 6707192550532129006341107)
    ·
      refine ⟨10060788825798193509511661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6707192550532129006341107 10060788825798193509511661)
      ·
        refine ⟨3772795809674322566066873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10060788825798193509511661 3772795809674322566066873)
        ·
          refine ⟨2829596857255741924550155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3772795809674322566066873 2829596857255741924550155)
          ·
            refine ⟨4244395285883612886825233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829596857255741924550155 4244395285883612886825233)
            ·
              refine ⟨3183296464412709665118925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4244395285883612886825233 3183296464412709665118925)
              ·
                refine ⟨1193736174154766124419597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3183296464412709665118925 1193736174154766124419597)
                ·
                  refine ⟨447651065308037296657349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193736174154766124419597 447651065308037296657349)
                  ·
                    rfl

theorem cell20_980772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_980772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980772 prefixEnd_980772 := by exact prefixLift 980772
  have htrace : WordTrace (prefixWord ++ tailWord_980772) baseStart_980772 baseEnd_980772 := by
    simpa [prefixWord, tailWord_980772, baseEnd_980772] using wordTrace_append hprefix tailTrace_980772
  have hstable : (prefixWord ++ tailWord_980772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980772).length < 2 ^ (prefixWord ++ tailWord_980772).sum := by decide
  have hdescent : baseEnd_980772 < baseStart_980772 := by decide
  rcases family_descends (prefixWord ++ tailWord_980772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980782 : List Nat := [4, 1, 3, 2, 2, 1, 3, 4]
def baseStart_980782 : Nat := 118140960795 + 980782 * 2 ^ 59
def prefixEnd_980782 : Nat := 4983230072969 + 3 ^ 40 * 980782 * 2
def baseEnd_980782 : Nat := 149218543193507235441325

theorem tailTrace_980782 : CollatzResearch.WordTrace tailWord_980782 prefixEnd_980782 149218543193507235441325 := by
  unfold tailWord_980782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4471507291600224134377075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23848038888534528716677733 4471507291600224134377075)
  ·
    refine ⟨6707260937400336201565613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4471507291600224134377075 6707260937400336201565613)
    ·
      refine ⟨2515222851525126075587105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6707260937400336201565613 2515222851525126075587105)
      ·
        refine ⟨1886417138643844556690329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2515222851525126075587105 1886417138643844556690329)
        ·
          refine ⟨1414812853982883417517747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1886417138643844556690329 1414812853982883417517747)
          ·
            refine ⟨2122219280974325126276621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414812853982883417517747 2122219280974325126276621)
            ·
              refine ⟨795832230365371922353733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2122219280974325126276621 795832230365371922353733)
              ·
                refine ⟨149218543193507235441325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 795832230365371922353733 149218543193507235441325)
                ·
                  rfl

theorem cell20_980782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_980782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980782 prefixEnd_980782 := by exact prefixLift 980782
  have htrace : WordTrace (prefixWord ++ tailWord_980782) baseStart_980782 baseEnd_980782 := by
    simpa [prefixWord, tailWord_980782, baseEnd_980782] using wordTrace_append hprefix tailTrace_980782
  have hstable : (prefixWord ++ tailWord_980782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980782).length < 2 ^ (prefixWord ++ tailWord_980782).sum := by decide
  have hdescent : baseEnd_980782 < baseStart_980782 := by decide
  rcases family_descends (prefixWord ++ tailWord_980782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980806 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_980806 : Nat := 118140960795 + 980806 * 2 ^ 59
def prefixEnd_980806 : Nat := 4983230072969 + 3 ^ 40 * 980806 * 2
def baseEnd_980806 : Nat := 447666583834484289523877

theorem tailTrace_980806 : CollatzResearch.WordTrace tailWord_980806 prefixEnd_980806 447666583834484289523877 := by
  unfold tailWord_980806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117904177647338911684071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23848622456476563449260181 1117904177647338911684071)
  ·
    refine ⟨1676856266471008367526107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1117904177647338911684071 1676856266471008367526107)
    ·
      refine ⟨2515284399706512551289161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1676856266471008367526107 2515284399706512551289161)
      ·
        refine ⟨1886463299779884413466871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2515284399706512551289161 1886463299779884413466871)
        ·
          refine ⟨2829694949669826620200307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886463299779884413466871 2829694949669826620200307)
          ·
            refine ⟨4244542424504739930300461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829694949669826620200307 4244542424504739930300461)
            ·
              refine ⟨1591703409189277473862673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4244542424504739930300461 1591703409189277473862673)
              ·
                refine ⟨1193777556891958105397005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1591703409189277473862673 1193777556891958105397005)
                ·
                  refine ⟨447666583834484289523877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193777556891958105397005 447666583834484289523877)
                  ·
                    rfl

theorem cell20_980806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_980806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980806 prefixEnd_980806 := by exact prefixLift 980806
  have htrace : WordTrace (prefixWord ++ tailWord_980806) baseStart_980806 baseEnd_980806 := by
    simpa [prefixWord, tailWord_980806, baseEnd_980806] using wordTrace_append hprefix tailTrace_980806
  have hstable : (prefixWord ++ tailWord_980806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980806).length < 2 ^ (prefixWord ++ tailWord_980806).sum := by decide
  have hdescent : baseEnd_980806 < baseStart_980806 := by decide
  rcases family_descends (prefixWord ++ tailWord_980806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980813 : List Nat := [1, 6, 1, 2, 1, 1, 2, 4, 2]
def baseStart_980813 : Nat := 118140960795 + 980813 * 2 ^ 59
def prefixEnd_980813 : Nat := 4983230072969 + 3 ^ 40 * 980813 * 2
def baseEnd_980813 : Nat := 447669778825223376290515

theorem tailTrace_980813 : CollatzResearch.WordTrace tailWord_980813 prefixEnd_980813 447669778825223376290515 := by
  unfold tailWord_980813
  simp only [CollatzResearch.WordTrace]
  refine ⟨35773188995689485369395093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23848792663792990246263395 35773188995689485369395093)
  ·
    refine ⟨1676868234172944626690395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35773188995689485369395093 1676868234172944626690395)
    ·
      refine ⟨2515302351259416940035593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1676868234172944626690395 2515302351259416940035593)
      ·
        refine ⟨1886476763444562705026695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2515302351259416940035593 1886476763444562705026695)
        ·
          refine ⟨2829715145166844057540043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886476763444562705026695 2829715145166844057540043)
          ·
            refine ⟨4244572717750266086310065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829715145166844057540043 4244572717750266086310065)
            ·
              refine ⟨3183429538312699564732549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4244572717750266086310065 3183429538312699564732549)
              ·
                refine ⟨596893038433631168387353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3183429538312699564732549 596893038433631168387353)
                ·
                  refine ⟨447669778825223376290515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596893038433631168387353 447669778825223376290515)
                  ·
                    rfl

theorem cell20_980813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_980813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980813 prefixEnd_980813 := by exact prefixLift 980813
  have htrace : WordTrace (prefixWord ++ tailWord_980813) baseStart_980813 baseEnd_980813 := by
    simpa [prefixWord, tailWord_980813, baseEnd_980813] using wordTrace_append hprefix tailTrace_980813
  have hstable : (prefixWord ++ tailWord_980813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980813).length < 2 ^ (prefixWord ++ tailWord_980813).sum := by decide
  have hdescent : baseEnd_980813 < baseStart_980813 := by decide
  rcases family_descends (prefixWord ++ tailWord_980813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980817 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 4]
def baseStart_980817 : Nat := 118140960795 + 980817 * 2 ^ 59
def prefixEnd_980817 : Nat := 4983230072969 + 3 ^ 40 * 980817 * 2
def baseEnd_980817 : Nat := 447671604534217140157165

theorem tailTrace_980817 : CollatzResearch.WordTrace tailWord_980817 prefixEnd_980817 447671604534217140157165 := by
  unfold tailWord_980817
  simp only [CollatzResearch.WordTrace]
  refine ⟨35773334887674994052540705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23848889925116662701693803 35773334887674994052540705)
  ·
    refine ⟨26830001165756245539405529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35773334887674994052540705 26830001165756245539405529)
    ·
      refine ⟨20122500874317184154554147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26830001165756245539405529 20122500874317184154554147)
      ·
        refine ⟨30183751311475776231831221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20122500874317184154554147 30183751311475776231831221)
        ·
          refine ⟨2829726685450854021734177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30183751311475776231831221 2829726685450854021734177)
          ·
            refine ⟨2122295014088140516300633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2829726685450854021734177 2122295014088140516300633)
            ·
              refine ⟨1591721260566105387225475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2122295014088140516300633 1591721260566105387225475)
              ·
                refine ⟨2387581890849158080838213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591721260566105387225475 2387581890849158080838213)
                ·
                  refine ⟨447671604534217140157165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2387581890849158080838213 447671604534217140157165)
                  ·
                    rfl

theorem cell20_980817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_980817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980817 prefixEnd_980817 := by exact prefixLift 980817
  have htrace : WordTrace (prefixWord ++ tailWord_980817) baseStart_980817 baseEnd_980817 := by
    simpa [prefixWord, tailWord_980817, baseEnd_980817] using wordTrace_append hprefix tailTrace_980817
  have hstable : (prefixWord ++ tailWord_980817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980817).length < 2 ^ (prefixWord ++ tailWord_980817).sum := by decide
  have hdescent : baseEnd_980817 < baseStart_980817 := by decide
  rcases family_descends (prefixWord ++ tailWord_980817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980869 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 3]
def baseStart_980869 : Nat := 118140960795 + 980869 * 2 ^ 59
def prefixEnd_980869 : Nat := 4983230072969 + 3 ^ 40 * 980869 * 2
def baseEnd_980869 : Nat := 447695338751136070423619

theorem tailTrace_980869 : CollatzResearch.WordTrace tailWord_980869 prefixEnd_980869 447695338751136070423619 := by
  unfold tailWord_980869
  simp only [CollatzResearch.WordTrace]
  refine ⟨35775231483486606933433661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23850154322324404622289107 35775231483486606933433661)
  ·
    refine ⟨13415711806307477600037623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35775231483486606933433661 13415711806307477600037623)
    ·
      refine ⟨20123567709461216400056435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13415711806307477600037623 20123567709461216400056435)
      ·
        refine ⟨30185351564191824600084653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20123567709461216400056435 30185351564191824600084653)
        ·
          refine ⟨11319506836571934225031745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30185351564191824600084653 11319506836571934225031745)
          ·
            refine ⟨8489630127428950668773809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11319506836571934225031745 8489630127428950668773809)
            ·
              refine ⟨6367222595571713001580357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8489630127428950668773809 6367222595571713001580357)
              ·
                refine ⟨1193854236669696187796317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6367222595571713001580357 1193854236669696187796317)
                ·
                  refine ⟨447695338751136070423619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193854236669696187796317 447695338751136070423619)
                  ·
                    rfl

theorem cell20_980869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_980869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980869 prefixEnd_980869 := by exact prefixLift 980869
  have htrace : WordTrace (prefixWord ++ tailWord_980869) baseStart_980869 baseEnd_980869 := by
    simpa [prefixWord, tailWord_980869, baseEnd_980869] using wordTrace_append hprefix tailTrace_980869
  have hstable : (prefixWord ++ tailWord_980869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980869).length < 2 ^ (prefixWord ++ tailWord_980869).sum := by decide
  have hdescent : baseEnd_980869 < baseStart_980869 := by decide
  rcases family_descends (prefixWord ++ tailWord_980869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980872 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 4]
def baseStart_980872 : Nat := 118140960795 + 980872 * 2 ^ 59
def prefixEnd_980872 : Nat := 4983230072969 + 3 ^ 40 * 980872 * 2
def baseEnd_980872 : Nat := 447696708032881393323607

theorem tailTrace_980872 : CollatzResearch.WordTrace tailWord_980872 prefixEnd_980872 447696708032881393323607 := by
  unfold tailWord_980872
  simp only [CollatzResearch.WordTrace]
  refine ⟨17887670451237869222896435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23850227268317158963861913 17887670451237869222896435)
  ·
    refine ⟨26831505676856803834344653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17887670451237869222896435 26831505676856803834344653)
    ·
      refine ⟨10061814628821301437879245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26831505676856803834344653 10061814628821301437879245)
      ·
        refine ⟨3773180485807988039204717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10061814628821301437879245 3773180485807988039204717)
        ·
          refine ⟨1414942682177995514701769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3773180485807988039204717 1414942682177995514701769)
          ·
            refine ⟨1061207011633496636026327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414942682177995514701769 1061207011633496636026327)
            ·
              refine ⟨1591810517450244954039491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061207011633496636026327 1591810517450244954039491)
              ·
                refine ⟨2387715776175367431059237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591810517450244954039491 2387715776175367431059237)
                ·
                  refine ⟨447696708032881393323607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2387715776175367431059237 447696708032881393323607)
                  ·
                    rfl

theorem cell20_980872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_980872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980872 prefixEnd_980872 := by exact prefixLift 980872
  have htrace : WordTrace (prefixWord ++ tailWord_980872) baseStart_980872 baseEnd_980872 := by
    simpa [prefixWord, tailWord_980872, baseEnd_980872] using wordTrace_append hprefix tailTrace_980872
  have hstable : (prefixWord ++ tailWord_980872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980872).length < 2 ^ (prefixWord ++ tailWord_980872).sum := by decide
  have hdescent : baseEnd_980872 < baseStart_980872 := by decide
  rcases family_descends (prefixWord ++ tailWord_980872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980882 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_980882 : Nat := 118140960795 + 980882 * 2 ^ 59
def prefixEnd_980882 : Nat := 4983230072969 + 3 ^ 40 * 980882 * 2
def baseEnd_980882 : Nat := 447701272305365802990233

theorem tailTrace_980882 : CollatzResearch.WordTrace tailWord_980882 prefixEnd_980882 447701272305365802990233 := by
  unfold tailWord_980882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8943926408109877538414225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23850470421626340102437933 8943926408109877538414225)
  ·
    refine ⟨6707944806082408153810669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8943926408109877538414225 6707944806082408153810669)
    ·
      refine ⟨2515479302280903057679001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6707944806082408153810669 2515479302280903057679001)
      ·
        refine ⟨1886609476710677293259251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2515479302280903057679001 1886609476710677293259251)
        ·
          refine ⟨2829914215066015939888877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886609476710677293259251 2829914215066015939888877)
          ·
            refine ⟨1061217830649755977458329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2829914215066015939888877 1061217830649755977458329)
            ·
              refine ⟨795913372987316983093747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061217830649755977458329 795913372987316983093747)
              ·
                refine ⟨1193870059480975474640621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795913372987316983093747 1193870059480975474640621)
                ·
                  refine ⟨447701272305365802990233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193870059480975474640621 447701272305365802990233)
                  ·
                    rfl

theorem cell20_980882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_980882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980882 prefixEnd_980882 := by exact prefixLift 980882
  have htrace : WordTrace (prefixWord ++ tailWord_980882) baseStart_980882 baseEnd_980882 := by
    simpa [prefixWord, tailWord_980882, baseEnd_980882] using wordTrace_append hprefix tailTrace_980882
  have hstable : (prefixWord ++ tailWord_980882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980882).length < 2 ^ (prefixWord ++ tailWord_980882).sum := by decide
  have hdescent : baseEnd_980882 < baseStart_980882 := by decide
  rcases family_descends (prefixWord ++ tailWord_980882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980952 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_980952 : Nat := 118140960795 + 980952 * 2 ^ 59
def prefixEnd_980952 : Nat := 4983230072969 + 3 ^ 40 * 980952 * 2
def baseEnd_980952 : Nat := 447733222212756670656613

theorem tailTrace_980952 : CollatzResearch.WordTrace tailWord_980952 prefixEnd_980952 447733222212756670656613 := by
  unfold tailWord_980952
  simp only [CollatzResearch.WordTrace]
  refine ⟨17889129371092956054352555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23852172494790608072470073 17889129371092956054352555)
  ·
    refine ⟨26833694056639434081528833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17889129371092956054352555 26833694056639434081528833)
    ·
      refine ⟨20125270542479575561146625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26833694056639434081528833 20125270542479575561146625)
      ·
        refine ⟨15093952906859681670859969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20125270542479575561146625 15093952906859681670859969)
        ·
          refine ⟨11320464680144761253144977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15093952906859681670859969 11320464680144761253144977)
          ·
            refine ⟨8490348510108570939858733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11320464680144761253144977 8490348510108570939858733)
            ·
              refine ⟨3183880691290714102447025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8490348510108570939858733 3183880691290714102447025)
              ·
                refine ⟨2387910518468035576835269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183880691290714102447025 2387910518468035576835269)
                ·
                  refine ⟨447733222212756670656613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2387910518468035576835269 447733222212756670656613)
                  ·
                    rfl

theorem cell20_980952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_980952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980952 prefixEnd_980952 := by exact prefixLift 980952
  have htrace : WordTrace (prefixWord ++ tailWord_980952) baseStart_980952 baseEnd_980952 := by
    simpa [prefixWord, tailWord_980952, baseEnd_980952] using wordTrace_append hprefix tailTrace_980952
  have hstable : (prefixWord ++ tailWord_980952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980952).length < 2 ^ (prefixWord ++ tailWord_980952).sum := by decide
  have hdescent : baseEnd_980952 < baseStart_980952 := by decide
  rcases family_descends (prefixWord ++ tailWord_980952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980996 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 3]
def baseStart_980996 : Nat := 118140960795 + 980996 * 2 ^ 59
def prefixEnd_980996 : Nat := 4983230072969 + 3 ^ 40 * 980996 * 2
def baseEnd_980996 : Nat := 447753305011688073189767

theorem tailTrace_980996 : CollatzResearch.WordTrace tailWord_980996 prefixEnd_980996 447753305011688073189767 := by
  unfold tailWord_980996
  simp only [CollatzResearch.WordTrace]
  refine ⟨17889931777013253811653421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23853242369351005082204561 17889931777013253811653421)
  ·
    refine ⟨6708724416379970179370033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17889931777013253811653421 6708724416379970179370033)
    ·
      refine ⟨5031543312284977634527525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6708724416379970179370033 5031543312284977634527525)
      ·
        refine ⟨943414371053433306473911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5031543312284977634527525 943414371053433306473911)
        ·
          refine ⟨1415121556580149959710867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943414371053433306473911 1415121556580149959710867)
          ·
            refine ⟨2122682334870224939566301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415121556580149959710867 2122682334870224939566301)
            ·
              refine ⟨796005875576334352337363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2122682334870224939566301 796005875576334352337363)
              ·
                refine ⟨1194008813364501528506045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796005875576334352337363 1194008813364501528506045)
                ·
                  refine ⟨447753305011688073189767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194008813364501528506045 447753305011688073189767)
                  ·
                    rfl

theorem cell20_980996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_980996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980996 prefixEnd_980996 := by exact prefixLift 980996
  have htrace : WordTrace (prefixWord ++ tailWord_980996) baseStart_980996 baseEnd_980996 := by
    simpa [prefixWord, tailWord_980996, baseEnd_980996] using wordTrace_append hprefix tailTrace_980996
  have hstable : (prefixWord ++ tailWord_980996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980996).length < 2 ^ (prefixWord ++ tailWord_980996).sum := by decide
  have hdescent : baseEnd_980996 < baseStart_980996 := by decide
  rcases family_descends (prefixWord ++ tailWord_980996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981000 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 3]
def baseStart_981000 : Nat := 118140960795 + 981000 * 2 ^ 59
def prefixEnd_981000 : Nat := 4983230072969 + 3 ^ 40 * 981000 * 2
def baseEnd_981000 : Nat := 447755130720681837056417

theorem tailTrace_981000 : CollatzResearch.WordTrace tailWord_981000 prefixEnd_981000 447755130720681837056417 := by
  unfold tailWord_981000
  simp only [CollatzResearch.WordTrace]
  refine ⟨17890004723006008153226227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23853339630674677537634969 17890004723006008153226227)
  ·
    refine ⟨26835007084509012229839341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17890004723006008153226227 26835007084509012229839341)
    ·
      refine ⟨10063127656690879586189753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26835007084509012229839341 10063127656690879586189753)
      ·
        refine ⟨7547345742518159689642315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10063127656690879586189753 7547345742518159689642315)
        ·
          refine ⟨11321018613777239534463473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7547345742518159689642315 11321018613777239534463473)
          ·
            refine ⟨8490763960332929650847605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11321018613777239534463473 8490763960332929650847605)
            ·
              refine ⟨796009121281212154766963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8490763960332929650847605 796009121281212154766963)
              ·
                refine ⟨1194013681921818232150445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796009121281212154766963 1194013681921818232150445)
                ·
                  refine ⟨447755130720681837056417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194013681921818232150445 447755130720681837056417)
                  ·
                    rfl

theorem cell20_981000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_981000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981000 prefixEnd_981000 := by exact prefixLift 981000
  have htrace : WordTrace (prefixWord ++ tailWord_981000) baseStart_981000 baseEnd_981000 := by
    simpa [prefixWord, tailWord_981000, baseEnd_981000] using wordTrace_append hprefix tailTrace_981000
  have hstable : (prefixWord ++ tailWord_981000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981000).length < 2 ^ (prefixWord ++ tailWord_981000).sum := by decide
  have hdescent : baseEnd_981000 < baseStart_981000 := by decide
  rcases family_descends (prefixWord ++ tailWord_981000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981021 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_981021 : Nat := 118140960795 + 981021 * 2 ^ 59
def prefixEnd_981021 : Nat := 4983230072969 + 3 ^ 40 * 981021 * 2
def baseEnd_981021 : Nat := 447764715692899097356331

theorem tailTrace_981021 : CollatzResearch.WordTrace tailWord_981021 prefixEnd_981021 447764715692899097356331 := by
  unfold tailWord_981021
  simp only [CollatzResearch.WordTrace]
  refine ⟨35780775378935936892966917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23853850252623957928644611 35780775378935936892966917)
  ·
    refine ⟨6708895383550488167431297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35780775378935936892966917 6708895383550488167431297)
    ·
      refine ⟨5031671537662866125573473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6708895383550488167431297 5031671537662866125573473)
      ·
        refine ⟨3773753653247149594180105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5031671537662866125573473 3773753653247149594180105)
        ·
          refine ⟨2830315239935362195635079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3773753653247149594180105 2830315239935362195635079)
          ·
            refine ⟨4245472859903043293452619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830315239935362195635079 4245472859903043293452619)
            ·
              refine ⟨6368209289854564940178929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245472859903043293452619 6368209289854564940178929)
              ·
                refine ⟨4776156967390923705134197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6368209289854564940178929 4776156967390923705134197)
                ·
                  refine ⟨447764715692899097356331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4776156967390923705134197 447764715692899097356331)
                  ·
                    rfl

theorem cell20_981021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_981021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981021 prefixEnd_981021 := by exact prefixLift 981021
  have htrace : WordTrace (prefixWord ++ tailWord_981021) baseStart_981021 baseEnd_981021 := by
    simpa [prefixWord, tailWord_981021, baseEnd_981021] using wordTrace_append hprefix tailTrace_981021
  have hstable : (prefixWord ++ tailWord_981021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981021).length < 2 ^ (prefixWord ++ tailWord_981021).sum := by decide
  have hdescent : baseEnd_981021 < baseStart_981021 := by decide
  rcases family_descends (prefixWord ++ tailWord_981021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981031 : List Nat := [1, 1, 7, 1, 2, 2, 6]
def baseStart_981031 : Nat := 118140960795 + 981031 * 2 ^ 59
def prefixEnd_981031 : Nat := 4983230072969 + 3 ^ 40 * 981031 * 2
def baseEnd_981031 : Nat := 49752142218375945224773

theorem tailTrace_981031 : CollatzResearch.WordTrace tailWord_981031 prefixEnd_981031 49752142218375945224773 := by
  unfold tailWord_981031
  simp only [CollatzResearch.WordTrace]
  refine ⟨35781140108899708600830947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23854093405933139067220631 35781140108899708600830947)
  ·
    refine ⟨53671710163349562901246421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35781140108899708600830947 53671710163349562901246421)
    ·
      refine ⟨1257930706953505380497963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 53671710163349562901246421 1257930706953505380497963)
      ·
        refine ⟨1886896060430258070746945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257930706953505380497963 1886896060430258070746945)
        ·
          refine ⟨1415172045322693553060209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1886896060430258070746945 1415172045322693553060209)
          ·
            refine ⟨1061379033992020164795157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1415172045322693553060209 1061379033992020164795157)
            ·
              refine ⟨49752142218375945224773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1061379033992020164795157 49752142218375945224773)
              ·
                rfl

theorem cell20_981031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 6].length) (baseStart_981031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981031 prefixEnd_981031 := by exact prefixLift 981031
  have htrace : WordTrace (prefixWord ++ tailWord_981031) baseStart_981031 baseEnd_981031 := by
    simpa [prefixWord, tailWord_981031, baseEnd_981031] using wordTrace_append hprefix tailTrace_981031
  have hstable : (prefixWord ++ tailWord_981031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981031).length < 2 ^ (prefixWord ++ tailWord_981031).sum := by decide
  have hdescent : baseEnd_981031 < baseStart_981031 := by decide
  rcases family_descends (prefixWord ++ tailWord_981031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981045 : List Nat := [1, 3, 3, 1, 1, 1, 2, 6, 2]
def baseStart_981045 : Nat := 118140960795 + 981045 * 2 ^ 59
def prefixEnd_981045 : Nat := 4983230072969 + 3 ^ 40 * 981045 * 2
def baseEnd_981045 : Nat := 447775669946861680556233

theorem tailTrace_981045 : CollatzResearch.WordTrace tailWord_981045 prefixEnd_981045 447775669946861680556233 := by
  unfold tailWord_981045
  simp only [CollatzResearch.WordTrace]
  refine ⟨35781650730848988991840589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23854433820565992661227059 35781650730848988991840589)
  ·
    refine ⟨13418119024068370871940221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35781650730848988991840589 13418119024068370871940221)
    ·
      refine ⟨5031794634025639076977583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13418119024068370871940221 5031794634025639076977583)
      ·
        refine ⟨7547691951038458615466375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5031794634025639076977583 7547691951038458615466375)
        ·
          refine ⟨11321537926557687923199563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7547691951038458615466375 11321537926557687923199563)
          ·
            refine ⟨16982306889836531884799345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11321537926557687923199563 16982306889836531884799345)
            ·
              refine ⟨12736730167377398913599509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16982306889836531884799345 12736730167377398913599509)
              ·
                refine ⟨597034226595815574074977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12736730167377398913599509 597034226595815574074977)
                ·
                  refine ⟨447775669946861680556233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597034226595815574074977 447775669946861680556233)
                  ·
                    rfl

theorem cell20_981045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_981045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981045 prefixEnd_981045 := by exact prefixLift 981045
  have htrace : WordTrace (prefixWord ++ tailWord_981045) baseStart_981045 baseEnd_981045 := by
    simpa [prefixWord, tailWord_981045, baseEnd_981045] using wordTrace_append hprefix tailTrace_981045
  have hstable : (prefixWord ++ tailWord_981045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981045).length < 2 ^ (prefixWord ++ tailWord_981045).sum := by decide
  have hdescent : baseEnd_981045 < baseStart_981045 := by decide
  rcases family_descends (prefixWord ++ tailWord_981045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981086 : List Nat := [4, 4, 1, 1, 3, 7]
def baseStart_981086 : Nat := 118140960795 + 981086 * 2 ^ 59
def prefixEnd_981086 : Nat := 4983230072969 + 3 ^ 40 * 981086 * 2
def baseEnd_981086 : Nat := 16584977165335102229237

theorem tailTrace_981086 : CollatzResearch.WordTrace tailWord_981086 prefixEnd_981086 16584977165335102229237 := by
  unfold tailWord_981086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472893265462556624260389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23855430749133635329388741 4472893265462556624260389)
  ·
    refine ⟨838667487274229367048823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4472893265462556624260389 838667487274229367048823)
    ·
      refine ⟨1258001230911344050573235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838667487274229367048823 1258001230911344050573235)
      ·
        refine ⟨1887001846367016075859853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1258001230911344050573235 1887001846367016075859853)
        ·
          refine ⟨707625692387631028447445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1887001846367016075859853 707625692387631028447445)
          ·
            refine ⟨16584977165335102229237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 707625692387631028447445 16584977165335102229237)
            ·
              rfl

theorem cell20_981086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 7].length) (baseStart_981086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981086 prefixEnd_981086 := by exact prefixLift 981086
  have htrace : WordTrace (prefixWord ++ tailWord_981086) baseStart_981086 baseEnd_981086 := by
    simpa [prefixWord, tailWord_981086, baseEnd_981086] using wordTrace_append hprefix tailTrace_981086
  have hstable : (prefixWord ++ tailWord_981086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981086).length < 2 ^ (prefixWord ++ tailWord_981086).sum := by decide
  have hdescent : baseEnd_981086 < baseStart_981086 := by decide
  rcases family_descends (prefixWord ++ tailWord_981086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981087 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_981087 : Nat := 118140960795 + 981087 * 2 ^ 59
def prefixEnd_981087 : Nat := 4983230072969 + 3 ^ 40 * 981087 * 2
def baseEnd_981087 : Nat := 447794839891296201156061

theorem tailTrace_981087 : CollatzResearch.WordTrace tailWord_981087 prefixEnd_981087 447794839891296201156061 := by
  unfold tailWord_981087
  simp only [CollatzResearch.WordTrace]
  refine ⟨35783182596696830164869515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23855455064464553443246343 35783182596696830164869515)
  ·
    refine ⟨53674773895045245247304273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35783182596696830164869515 53674773895045245247304273)
    ·
      refine ⟨40256080421283933935478205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53674773895045245247304273 40256080421283933935478205)
      ·
        refine ⟨15096030157981475225804327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40256080421283933935478205 15096030157981475225804327)
        ·
          refine ⟨22644045236972212838706491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15096030157981475225804327 22644045236972212838706491)
          ·
            refine ⟨33966067855458319258059737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22644045236972212838706491 33966067855458319258059737)
            ·
              refine ⟨25474550891593739443544803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33966067855458319258059737 25474550891593739443544803)
              ·
                refine ⟨38211826337390609165317205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25474550891593739443544803 38211826337390609165317205)
                ·
                  refine ⟨447794839891296201156061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38211826337390609165317205 447794839891296201156061)
                  ·
                    rfl

theorem cell20_981087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_981087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981087 prefixEnd_981087 := by exact prefixLift 981087
  have htrace : WordTrace (prefixWord ++ tailWord_981087) baseStart_981087 baseEnd_981087 := by
    simpa [prefixWord, tailWord_981087, baseEnd_981087] using wordTrace_append hprefix tailTrace_981087
  have hstable : (prefixWord ++ tailWord_981087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981087).length < 2 ^ (prefixWord ++ tailWord_981087).sum := by decide
  have hdescent : baseEnd_981087 < baseStart_981087 := by decide
  rcases family_descends (prefixWord ++ tailWord_981087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981090 : List Nat := [3, 3, 2, 2, 2, 8]
def baseStart_981090 : Nat := 118140960795 + 981090 * 2 ^ 59
def prefixEnd_981090 : Nat := 4983230072969 + 3 ^ 40 * 981090 * 2
def baseEnd_981090 : Nat := 16585044784186723113187

theorem tailTrace_981090 : CollatzResearch.WordTrace tailWord_981090 prefixEnd_981090 16585044784186723113187 := by
  unfold tailWord_981090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8945823003921490419307181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23855528010457307784819149 8945823003921490419307181)
  ·
    refine ⟨3354683626470558907240193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8945823003921490419307181 3354683626470558907240193)
    ·
      refine ⟨2516012719852919180430145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3354683626470558907240193 2516012719852919180430145)
      ·
        refine ⟨1887009539889689385322609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2516012719852919180430145 1887009539889689385322609)
        ·
          refine ⟨1415257154917267038991957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1887009539889689385322609 1415257154917267038991957)
          ·
            refine ⟨16585044784186723113187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1415257154917267038991957 16585044784186723113187)
            ·
              rfl

theorem cell20_981090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 8].length) (baseStart_981090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981090 prefixEnd_981090 := by exact prefixLift 981090
  have htrace : WordTrace (prefixWord ++ tailWord_981090) baseStart_981090 baseEnd_981090 := by
    simpa [prefixWord, tailWord_981090, baseEnd_981090] using wordTrace_append hprefix tailTrace_981090
  have hstable : (prefixWord ++ tailWord_981090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981090).length < 2 ^ (prefixWord ++ tailWord_981090).sum := by decide
  have hdescent : baseEnd_981090 < baseStart_981090 := by decide
  rcases family_descends (prefixWord ++ tailWord_981090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981097 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 3]
def baseStart_981097 : Nat := 118140960795 + 981097 * 2 ^ 59
def prefixEnd_981097 : Nat := 4983230072969 + 3 ^ 40 * 981097 * 2
def baseEnd_981097 : Nat := 447799404163780610822687

theorem tailTrace_981097 : CollatzResearch.WordTrace tailWord_981097 prefixEnd_981097 447799404163780610822687 := by
  unfold tailWord_981097
  simp only [CollatzResearch.WordTrace]
  refine ⟨35783547326660601872733545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23855698217773734581822363 35783547326660601872733545)
  ·
    refine ⟨26837660494995451404550159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35783547326660601872733545 26837660494995451404550159)
    ·
      refine ⟨40256490742493177106825239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26837660494995451404550159 40256490742493177106825239)
      ·
        refine ⟨60384736113739765660237859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40256490742493177106825239 60384736113739765660237859)
        ·
          refine ⟨90577104170609648490356789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60384736113739765660237859 90577104170609648490356789)
          ·
            refine ⟨8491603515994654545970949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90577104170609648490356789 8491603515994654545970949)
            ·
              refine ⟨1592175659248997727369553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8491603515994654545970949 1592175659248997727369553)
              ·
                refine ⟨1194131744436748295527165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592175659248997727369553 1194131744436748295527165)
                ·
                  refine ⟨447799404163780610822687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194131744436748295527165 447799404163780610822687)
                  ·
                    rfl

theorem cell20_981097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_981097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981097 prefixEnd_981097 := by exact prefixLift 981097
  have htrace : WordTrace (prefixWord ++ tailWord_981097) baseStart_981097 baseEnd_981097 := by
    simpa [prefixWord, tailWord_981097, baseEnd_981097] using wordTrace_append hprefix tailTrace_981097
  have hstable : (prefixWord ++ tailWord_981097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981097).length < 2 ^ (prefixWord ++ tailWord_981097).sum := by decide
  have hdescent : baseEnd_981097 < baseStart_981097 := by decide
  rcases family_descends (prefixWord ++ tailWord_981097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981100 : List Nat := [2, 2, 1, 1, 3, 3, 4, 2, 2]
def baseStart_981100 : Nat := 118140960795 + 981100 * 2 ^ 59
def prefixEnd_981100 : Nat := 4983230072969 + 3 ^ 40 * 981100 * 2
def baseEnd_981100 : Nat := 447800773445525933722675

theorem tailTrace_981100 : CollatzResearch.WordTrace tailWord_981100 prefixEnd_981100 447800773445525933722675 := by
  unfold tailWord_981100
  simp only [CollatzResearch.WordTrace]
  refine ⟨17891828372824866692546377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23855771163766488923395169 17891828372824866692546377)
  ·
    refine ⟨13418871279618650019409783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17891828372824866692546377 13418871279618650019409783)
    ·
      refine ⟨20128306919427975029114675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13418871279618650019409783 20128306919427975029114675)
      ·
        refine ⟨30192460379141962543672013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20128306919427975029114675 30192460379141962543672013)
        ·
          refine ⟨11322172642178235953877005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30192460379141962543672013 11322172642178235953877005)
          ·
            refine ⟨4245814740816838482703877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11322172642178235953877005 4245814740816838482703877)
            ·
              refine ⟨796090263903157215506977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4245814740816838482703877 796090263903157215506977)
              ·
                refine ⟨597067697927367911630233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796090263903157215506977 597067697927367911630233)
                ·
                  refine ⟨447800773445525933722675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597067697927367911630233 447800773445525933722675)
                  ·
                    rfl

theorem cell20_981100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_981100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981100 prefixEnd_981100 := by exact prefixLift 981100
  have htrace : WordTrace (prefixWord ++ tailWord_981100) baseStart_981100 baseEnd_981100 := by
    simpa [prefixWord, tailWord_981100, baseEnd_981100] using wordTrace_append hprefix tailTrace_981100
  have hstable : (prefixWord ++ tailWord_981100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981100).length < 2 ^ (prefixWord ++ tailWord_981100).sum := by decide
  have hdescent : baseEnd_981100 < baseStart_981100 := by decide
  rcases family_descends (prefixWord ++ tailWord_981100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981111 : List Nat := [1, 1, 3, 1, 1, 5, 3, 5]
def baseStart_981111 : Nat := 118140960795 + 981111 * 2 ^ 59
def prefixEnd_981111 : Nat := 4983230072969 + 3 ^ 40 * 981111 * 2
def baseEnd_981111 : Nat := 149268598048419594785321

theorem tailTrace_981111 : CollatzResearch.WordTrace tailWord_981111 prefixEnd_981111 149268598048419594785321 := by
  unfold tailWord_981111
  simp only [CollatzResearch.WordTrace]
  refine ⟨35784057948609882263743187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23856038632406588175828791 35784057948609882263743187)
  ·
    refine ⟨53676086922914823395614781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35784057948609882263743187 53676086922914823395614781)
    ·
      refine ⟨20128532596093058773355543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53676086922914823395614781 20128532596093058773355543)
      ·
        refine ⟨30192798894139588160033315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20128532596093058773355543 30192798894139588160033315)
        ·
          refine ⟨45289198341209382240049973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30192798894139588160033315 45289198341209382240049973)
          ·
            refine ⟨4245862344488379585004685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45289198341209382240049973 4245862344488379585004685)
            ·
              refine ⟨1592198379183142344376757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4245862344488379585004685 1592198379183142344376757)
              ·
                refine ⟨149268598048419594785321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1592198379183142344376757 149268598048419594785321)
                ·
                  rfl

theorem cell20_981111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_981111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981111 prefixEnd_981111 := by exact prefixLift 981111
  have htrace : WordTrace (prefixWord ++ tailWord_981111) baseStart_981111 baseEnd_981111 := by
    simpa [prefixWord, tailWord_981111, baseEnd_981111] using wordTrace_append hprefix tailTrace_981111
  have hstable : (prefixWord ++ tailWord_981111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981111).length < 2 ^ (prefixWord ++ tailWord_981111).sum := by decide
  have hdescent : baseEnd_981111 < baseStart_981111 := by decide
  rcases family_descends (prefixWord ++ tailWord_981111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981121 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 4]
def baseStart_981121 : Nat := 118140960795 + 981121 * 2 ^ 59
def prefixEnd_981121 : Nat := 4983230072969 + 3 ^ 40 * 981121 * 2
def baseEnd_981121 : Nat := 447810358417743194022589

theorem tailTrace_981121 : CollatzResearch.WordTrace tailWord_981121 prefixEnd_981121 447810358417743194022589 := by
  unfold tailWord_981121
  simp only [CollatzResearch.WordTrace]
  refine ⟨35784422678573653971607217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23856281785715769314404811 35784422678573653971607217)
  ·
    refine ⟨26838317008930240478705413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35784422678573653971607217 26838317008930240478705413)
    ·
      refine ⟨5032184439174420089757265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26838317008930240478705413 5032184439174420089757265)
      ·
        refine ⟨3774138329380815067317949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5032184439174420089757265 3774138329380815067317949)
        ·
          refine ⟨1415301873517805650244231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3774138329380815067317949 1415301873517805650244231)
          ·
            refine ⟨2122952810276708475366347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415301873517805650244231 2122952810276708475366347)
            ·
              refine ⟨3184429215415062713049521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122952810276708475366347 3184429215415062713049521)
              ·
                refine ⟨2388321911561297034787141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3184429215415062713049521 2388321911561297034787141)
                ·
                  refine ⟨447810358417743194022589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388321911561297034787141 447810358417743194022589)
                  ·
                    rfl

theorem cell20_981121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_981121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981121 prefixEnd_981121 := by exact prefixLift 981121
  have htrace : WordTrace (prefixWord ++ tailWord_981121) baseStart_981121 baseEnd_981121 := by
    simpa [prefixWord, tailWord_981121, baseEnd_981121] using wordTrace_append hprefix tailTrace_981121
  have hstable : (prefixWord ++ tailWord_981121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981121).length < 2 ^ (prefixWord ++ tailWord_981121).sum := by decide
  have hdescent : baseEnd_981121 < baseStart_981121 := by decide
  rcases family_descends (prefixWord ++ tailWord_981121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981138 : List Nat := [3, 2, 3, 1, 1, 1, 4, 3, 2]
def baseStart_981138 : Nat := 118140960795 + 981138 * 2 ^ 59
def prefixEnd_981138 : Nat := 4983230072969 + 3 ^ 40 * 981138 * 2
def baseEnd_981138 : Nat := 447818117680966690455853

theorem tailTrace_981138 : CollatzResearch.WordTrace tailWord_981138 prefixEnd_981138 447818117680966690455853 := by
  unfold tailWord_981138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8946260679878016468744017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23856695146341377249984045 8946260679878016468744017)
  ·
    refine ⟨6709695509908512351558013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8946260679878016468744017 6709695509908512351558013)
    ·
      refine ⟨2516135816215692131834255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6709695509908512351558013 2516135816215692131834255)
      ·
        refine ⟨3774203724323538197751383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516135816215692131834255 3774203724323538197751383)
        ·
          refine ⟨5661305586485307296627075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774203724323538197751383 5661305586485307296627075)
          ·
            refine ⟨8491958379727960944940613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661305586485307296627075 8491958379727960944940613)
            ·
              refine ⟨1592242196198992677176365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8491958379727960944940613 1592242196198992677176365)
              ·
                refine ⟨597090823574622253941137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1592242196198992677176365 597090823574622253941137)
                ·
                  refine ⟨447818117680966690455853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597090823574622253941137 447818117680966690455853)
                  ·
                    rfl

theorem cell20_981138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_981138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981138 prefixEnd_981138 := by exact prefixLift 981138
  have htrace : WordTrace (prefixWord ++ tailWord_981138) baseStart_981138 baseEnd_981138 := by
    simpa [prefixWord, tailWord_981138, baseEnd_981138] using wordTrace_append hprefix tailTrace_981138
  have hstable : (prefixWord ++ tailWord_981138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981138).length < 2 ^ (prefixWord ++ tailWord_981138).sum := by decide
  have hdescent : baseEnd_981138 < baseStart_981138 := by decide
  rcases family_descends (prefixWord ++ tailWord_981138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981149 : List Nat := [1, 4, 2, 1, 1, 4, 7]
def baseStart_981149 : Nat := 118140960795 + 981149 * 2 ^ 59
def prefixEnd_981149 : Nat := 4983230072969 + 3 ^ 40 * 981149 * 2
def baseEnd_981149 : Nat := 49758126486744393454349

theorem tailTrace_981149 : CollatzResearch.WordTrace tailWord_981149 prefixEnd_981149 49758126486744393454349 := by
  unfold tailWord_981149
  simp only [CollatzResearch.WordTrace]
  refine ⟨35785443922472214753626501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23856962614981476502417667 35785443922472214753626501)
  ·
    refine ⟨6709770735463540266304969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35785443922472214753626501 6709770735463540266304969)
    ·
      refine ⟨5032328051597655199728727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6709770735463540266304969 5032328051597655199728727)
      ·
        refine ⟨7548492077396482799593091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5032328051597655199728727 7548492077396482799593091)
        ·
          refine ⟨11322738116094724199389637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7548492077396482799593091 11322738116094724199389637)
          ·
            refine ⟨2123013396767760787385557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11322738116094724199389637 2123013396767760787385557)
            ·
              refine ⟨49758126486744393454349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2123013396767760787385557 49758126486744393454349)
              ·
                rfl

theorem cell20_981149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 7].length) (baseStart_981149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981149 prefixEnd_981149 := by exact prefixLift 981149
  have htrace : WordTrace (prefixWord ++ tailWord_981149) baseStart_981149 baseEnd_981149 := by
    simpa [prefixWord, tailWord_981149, baseEnd_981149] using wordTrace_append hprefix tailTrace_981149
  have hstable : (prefixWord ++ tailWord_981149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981149).length < 2 ^ (prefixWord ++ tailWord_981149).sum := by decide
  have hdescent : baseEnd_981149 < baseStart_981149 := by decide
  rcases family_descends (prefixWord ++ tailWord_981149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981152 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 3]
def baseStart_981152 : Nat := 118140960795 + 981152 * 2 ^ 59
def prefixEnd_981152 : Nat := 4983230072969 + 3 ^ 40 * 981152 * 2
def baseEnd_981152 : Nat := 447824507662444863989129

theorem tailTrace_981152 : CollatzResearch.WordTrace tailWord_981152 prefixEnd_981152 447824507662444863989129 := by
  unfold tailWord_981152
  simp only [CollatzResearch.WordTrace]
  refine ⟨17892776670730673132992855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23857035560974230843990473 17892776670730673132992855)
  ·
    refine ⟨26839165006096009699489283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17892776670730673132992855 26839165006096009699489283)
    ·
      refine ⟨40258747509144014549233925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26839165006096009699489283 40258747509144014549233925)
      ·
        refine ⟨7548515157964502727981361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40258747509144014549233925 7548515157964502727981361)
        ·
          refine ⟨5661386368473377045986021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7548515157964502727981361 5661386368473377045986021)
          ·
            refine ⟨1061509944088758196122379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5661386368473377045986021 1061509944088758196122379)
            ·
              refine ⟨1592264916133137294183569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061509944088758196122379 1592264916133137294183569)
              ·
                refine ⟨1194198687099852970637677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592264916133137294183569 1194198687099852970637677)
                ·
                  refine ⟨447824507662444863989129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194198687099852970637677 447824507662444863989129)
                  ·
                    rfl

theorem cell20_981152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_981152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981152 prefixEnd_981152 := by exact prefixLift 981152
  have htrace : WordTrace (prefixWord ++ tailWord_981152) baseStart_981152 baseEnd_981152 := by
    simpa [prefixWord, tailWord_981152, baseEnd_981152] using wordTrace_append hprefix tailTrace_981152
  have hstable : (prefixWord ++ tailWord_981152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981152).length < 2 ^ (prefixWord ++ tailWord_981152).sum := by decide
  have hdescent : baseEnd_981152 < baseStart_981152 := by decide
  rcases family_descends (prefixWord ++ tailWord_981152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981169 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 3]
def baseStart_981169 : Nat := 118140960795 + 981169 * 2 ^ 59
def prefixEnd_981169 : Nat := 4983230072969 + 3 ^ 40 * 981169 * 2
def baseEnd_981169 : Nat := 447832266925668360422393

theorem tailTrace_981169 : CollatzResearch.WordTrace tailWord_981169 prefixEnd_981169 447832266925668360422393 := by
  unfold tailWord_981169
  simp only [CollatzResearch.WordTrace]
  refine ⟨35786173382399758169354561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23857448921599838779569707 35786173382399758169354561)
  ·
    refine ⟨26839630036799818627015921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35786173382399758169354561 26839630036799818627015921)
    ·
      refine ⟨20129722527599863970261941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26839630036799818627015921 20129722527599863970261941)
      ·
        refine ⟨1887161486962487247212057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20129722527599863970261941 1887161486962487247212057)
        ·
          refine ⟨1415371115221865435409043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1887161486962487247212057 1415371115221865435409043)
          ·
            refine ⟨2123056672832798153113565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415371115221865435409043 2123056672832798153113565)
            ·
              refine ⟨796146252312299307417587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2123056672832798153113565 796146252312299307417587)
              ·
                refine ⟨1194219378468448961126381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796146252312299307417587 1194219378468448961126381)
                ·
                  refine ⟨447832266925668360422393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194219378468448961126381 447832266925668360422393)
                  ·
                    rfl

theorem cell20_981169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_981169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981169 prefixEnd_981169 := by exact prefixLift 981169
  have htrace : WordTrace (prefixWord ++ tailWord_981169) baseStart_981169 baseEnd_981169 := by
    simpa [prefixWord, tailWord_981169, baseEnd_981169] using wordTrace_append hprefix tailTrace_981169
  have hstable : (prefixWord ++ tailWord_981169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981169).length < 2 ^ (prefixWord ++ tailWord_981169).sum := by decide
  have hdescent : baseEnd_981169 < baseStart_981169 := by decide
  rcases family_descends (prefixWord ++ tailWord_981169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981194 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_981194 : Nat := 118140960795 + 981194 * 2 ^ 59
def prefixEnd_981194 : Nat := 4983230072969 + 3 ^ 40 * 981194 * 2
def baseEnd_981194 : Nat := 447843677606879384588957

theorem tailTrace_981194 : CollatzResearch.WordTrace tailWord_981194 prefixEnd_981194 447843677606879384588957 := by
  unfold tailWord_981194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8946771301827296859753659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23858056804872791626009757 8946771301827296859753659)
  ·
    refine ⟨13420156952740945289630489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8946771301827296859753659 13420156952740945289630489)
    ·
      refine ⟨10065117714555708967222867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13420156952740945289630489 10065117714555708967222867)
      ·
        refine ⟨15097676571833563450834301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10065117714555708967222867 15097676571833563450834301)
        ·
          refine ⟨5661628714437586294062863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15097676571833563450834301 5661628714437586294062863)
          ·
            refine ⟨8492443071656379441094295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661628714437586294062863 8492443071656379441094295)
            ·
              refine ⟨12738664607484569161641443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8492443071656379441094295 12738664607484569161641443)
              ·
                refine ⟨19107996911226853742462165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12738664607484569161641443 19107996911226853742462165)
                ·
                  refine ⟨447843677606879384588957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19107996911226853742462165 447843677606879384588957)
                  ·
                    rfl

theorem cell20_981194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_981194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981194 prefixEnd_981194 := by exact prefixLift 981194
  have htrace : WordTrace (prefixWord ++ tailWord_981194) baseStart_981194 baseEnd_981194 := by
    simpa [prefixWord, tailWord_981194, baseEnd_981194] using wordTrace_append hprefix tailTrace_981194
  have hstable : (prefixWord ++ tailWord_981194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981194).length < 2 ^ (prefixWord ++ tailWord_981194).sum := by decide
  have hdescent : baseEnd_981194 < baseStart_981194 := by decide
  rcases family_descends (prefixWord ++ tailWord_981194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981201 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_981201 : Nat := 118140960795 + 981201 * 2 ^ 59
def prefixEnd_981201 : Nat := 4983230072969 + 3 ^ 40 * 981201 * 2
def baseEnd_981201 : Nat := 447846872597618471355595

theorem tailTrace_981201 : CollatzResearch.WordTrace tailWord_981201 prefixEnd_981201 447846872597618471355595 := by
  unfold tailWord_981201
  simp only [CollatzResearch.WordTrace]
  refine ⟨35787340518283827634519457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23858227012189218423012971 35787340518283827634519457)
  ·
    refine ⟨26840505388712870725889593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35787340518283827634519457 26840505388712870725889593)
    ·
      refine ⟨20130379041534653044417195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26840505388712870725889593 20130379041534653044417195)
      ·
        refine ⟨30195568562301979566625793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20130379041534653044417195 30195568562301979566625793)
        ·
          refine ⟨22646676421726484674969345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30195568562301979566625793 22646676421726484674969345)
          ·
            refine ⟨16985007316294863506227009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22646676421726484674969345 16985007316294863506227009)
            ·
              refine ⟨12738755487221147629670257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16985007316294863506227009 12738755487221147629670257)
              ·
                refine ⟨9554066615415860722252693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12738755487221147629670257 9554066615415860722252693)
                ·
                  refine ⟨447846872597618471355595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9554066615415860722252693 447846872597618471355595)
                  ·
                    rfl

theorem cell20_981201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_981201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981201 prefixEnd_981201 := by exact prefixLift 981201
  have htrace : WordTrace (prefixWord ++ tailWord_981201) baseStart_981201 baseEnd_981201 := by
    simpa [prefixWord, tailWord_981201, baseEnd_981201] using wordTrace_append hprefix tailTrace_981201
  have hstable : (prefixWord ++ tailWord_981201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981201).length < 2 ^ (prefixWord ++ tailWord_981201).sum := by decide
  have hdescent : baseEnd_981201 < baseStart_981201 := by decide
  rcases family_descends (prefixWord ++ tailWord_981201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981280 : List Nat := [2, 1, 1, 5, 2, 3, 1, 5]
def baseStart_981280 : Nat := 118140960795 + 981280 * 2 ^ 59
def prefixEnd_981280 : Nat := 4983230072969 + 3 ^ 40 * 981280 * 2
def baseEnd_981280 : Nat := 149294310116748435907313

theorem tailTrace_981280 : CollatzResearch.WordTrace tailWord_981280 prefixEnd_981280 149294310116748435907313 := by
  unfold tailWord_981280
  simp only [CollatzResearch.WordTrace]
  refine ⟨17895110942498812063322647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23860147923331749417763529 17895110942498812063322647)
  ·
    refine ⟨26842666413748218094983971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17895110942498812063322647 26842666413748218094983971)
    ·
      refine ⟨40263999620622327142475957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26842666413748218094983971 40263999620622327142475957)
      ·
        refine ⟨3774749964433343169607121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40263999620622327142475957 3774749964433343169607121)
        ·
          refine ⟨2831062473325007377205341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3774749964433343169607121 2831062473325007377205341)
          ·
            refine ⟨1061648427496877766452003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2831062473325007377205341 1061648427496877766452003)
            ·
              refine ⟨1592472641245316649678005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061648427496877766452003 1592472641245316649678005)
              ·
                refine ⟨149294310116748435907313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1592472641245316649678005 149294310116748435907313)
                ·
                  rfl

theorem cell20_981280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_981280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981280 prefixEnd_981280 := by exact prefixLift 981280
  have htrace : WordTrace (prefixWord ++ tailWord_981280) baseStart_981280 baseEnd_981280 := by
    simpa [prefixWord, tailWord_981280, baseEnd_981280] using wordTrace_append hprefix tailTrace_981280
  have hstable : (prefixWord ++ tailWord_981280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981280).length < 2 ^ (prefixWord ++ tailWord_981280).sum := by decide
  have hdescent : baseEnd_981280 < baseStart_981280 := by decide
  rcases family_descends (prefixWord ++ tailWord_981280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981308 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_981308 : Nat := 118140960795 + 981308 * 2 ^ 59
def prefixEnd_981308 : Nat := 4983230072969 + 3 ^ 40 * 981308 * 2
def baseEnd_981308 : Nat := 447895710313201654788491

theorem tailTrace_981308 : CollatzResearch.WordTrace tailWord_981308 prefixEnd_981308 447895710313201654788491 := by
  unfold tailWord_981308
  simp only [CollatzResearch.WordTrace]
  refine ⟨17895621564448092454332289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23860828752597456605776385 17895621564448092454332289)
  ·
    refine ⟨13421716173336069340749217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17895621564448092454332289 13421716173336069340749217)
    ·
      refine ⟨10066287130002052005561913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13421716173336069340749217 10066287130002052005561913)
      ·
        refine ⟨7549715347501539004171435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10066287130002052005561913 7549715347501539004171435)
        ·
          refine ⟨11324573021252308506257153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7549715347501539004171435 11324573021252308506257153)
          ·
            refine ⟨8493429765939231379692865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11324573021252308506257153 8493429765939231379692865)
            ·
              refine ⟨6370072324454423534769649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8493429765939231379692865 6370072324454423534769649)
              ·
                refine ⟨4777554243340817651077237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6370072324454423534769649 4777554243340817651077237)
                ·
                  refine ⟨447895710313201654788491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4777554243340817651077237 447895710313201654788491)
                  ·
                    rfl

theorem cell20_981308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_981308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981308 prefixEnd_981308 := by exact prefixLift 981308
  have htrace : WordTrace (prefixWord ++ tailWord_981308) baseStart_981308 baseEnd_981308 := by
    simpa [prefixWord, tailWord_981308, baseEnd_981308] using wordTrace_append hprefix tailTrace_981308
  have hstable : (prefixWord ++ tailWord_981308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981308).length < 2 ^ (prefixWord ++ tailWord_981308).sum := by decide
  have hdescent : baseEnd_981308 < baseStart_981308 := by decide
  rcases family_descends (prefixWord ++ tailWord_981308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981311 : List Nat := [1, 1, 2, 2, 4, 1, 4, 3, 2]
def baseStart_981311 : Nat := 118140960795 + 981311 * 2 ^ 59
def prefixEnd_981311 : Nat := 4983230072969 + 3 ^ 40 * 981311 * 2
def baseEnd_981311 : Nat := 447897079594946977688479

theorem tailTrace_981311 : CollatzResearch.WordTrace tailWord_981311 prefixEnd_981311 447897079594946977688479 := by
  unfold tailWord_981311
  simp only [CollatzResearch.WordTrace]
  refine ⟨35791352547885316421023787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23860901698590210947349191 35791352547885316421023787)
  ·
    refine ⟨53687028821827974631535681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35791352547885316421023787 53687028821827974631535681)
    ·
      refine ⟨40265271616370980973651761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53687028821827974631535681 40265271616370980973651761)
      ·
        refine ⟨30198953712278235730238821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40265271616370980973651761 30198953712278235730238821)
        ·
          refine ⟨5662303821052169199419779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30198953712278235730238821 5662303821052169199419779)
          ·
            refine ⟨8493455731578253799129669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662303821052169199419779 8493455731578253799129669)
            ·
              refine ⟨1592522949670922587336813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8493455731578253799129669 1592522949670922587336813)
              ·
                refine ⟨597196106126595970251305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1592522949670922587336813 597196106126595970251305)
                ·
                  refine ⟨447897079594946977688479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597196106126595970251305 447897079594946977688479)
                  ·
                    rfl

theorem cell20_981311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 2].length) (baseStart_981311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981311 prefixEnd_981311 := by exact prefixLift 981311
  have htrace : WordTrace (prefixWord ++ tailWord_981311) baseStart_981311 baseEnd_981311 := by
    simpa [prefixWord, tailWord_981311, baseEnd_981311] using wordTrace_append hprefix tailTrace_981311
  have hstable : (prefixWord ++ tailWord_981311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981311).length < 2 ^ (prefixWord ++ tailWord_981311).sum := by decide
  have hdescent : baseEnd_981311 < baseStart_981311 := by decide
  rcases family_descends (prefixWord ++ tailWord_981311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981332 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_981332 : Nat := 118140960795 + 981332 * 2 ^ 59
def prefixEnd_981332 : Nat := 4983230072969 + 3 ^ 40 * 981332 * 2
def baseEnd_981332 : Nat := 447906664567164237988393

theorem tailTrace_981332 : CollatzResearch.WordTrace tailWord_981332 prefixEnd_981332 447906664567164237988393 := by
  unfold tailWord_981332
  simp only [CollatzResearch.WordTrace]
  refine ⟨17896059240404618503769125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23861412320539491338358833 17896059240404618503769125)
  ·
    refine ⟨3355511107575865969456711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17896059240404618503769125 3355511107575865969456711)
    ·
      refine ⟨5033266661363798954185067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3355511107575865969456711 5033266661363798954185067)
      ·
        refine ⟨7549899992045698431277601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5033266661363798954185067 7549899992045698431277601)
        ·
          refine ⟨5662424994034273823458201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7549899992045698431277601 5662424994034273823458201)
          ·
            refine ⟨4246818745525705367593651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5662424994034273823458201 4246818745525705367593651)
            ·
              refine ⟨6370228118288558051390477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4246818745525705367593651 6370228118288558051390477)
              ·
                refine ⟨2388835544358209269271429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6370228118288558051390477 2388835544358209269271429)
                ·
                  refine ⟨447906664567164237988393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388835544358209269271429 447906664567164237988393)
                  ·
                    rfl

theorem cell20_981332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_981332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981332 prefixEnd_981332 := by exact prefixLift 981332
  have htrace : WordTrace (prefixWord ++ tailWord_981332) baseStart_981332 baseEnd_981332 := by
    simpa [prefixWord, tailWord_981332, baseEnd_981332] using wordTrace_append hprefix tailTrace_981332
  have hstable : (prefixWord ++ tailWord_981332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981332).length < 2 ^ (prefixWord ++ tailWord_981332).sum := by decide
  have hdescent : baseEnd_981332 < baseStart_981332 := by decide
  rcases family_descends (prefixWord ++ tailWord_981332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981353 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_981353 : Nat := 118140960795 + 981353 * 2 ^ 59
def prefixEnd_981353 : Nat := 4983230072969 + 3 ^ 40 * 981353 * 2
def baseEnd_981353 : Nat := 447916249539381498288307

theorem tailTrace_981353 : CollatzResearch.WordTrace tailWord_981353 prefixEnd_981353 447916249539381498288307 := by
  unfold tailWord_981353
  simp only [CollatzResearch.WordTrace]
  refine ⟨35792884413733157594052713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23861922942488771729368475 35792884413733157594052713)
  ·
    refine ⟨26844663310299868195539535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35792884413733157594052713 26844663310299868195539535)
    ·
      refine ⟨40266994965449802293309303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26844663310299868195539535 40266994965449802293309303)
      ·
        refine ⟨60400492448174703439963955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40266994965449802293309303 60400492448174703439963955)
        ·
          refine ⟨90600738672262055159945933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60400492448174703439963955 90600738672262055159945933)
          ·
            refine ⟨33975277002098270684979725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90600738672262055159945933 33975277002098270684979725)
            ·
              refine ⟨12740728875786851506867397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33975277002098270684979725 12740728875786851506867397)
              ·
                refine ⟨2388886664210034657537637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12740728875786851506867397 2388886664210034657537637)
                ·
                  refine ⟨447916249539381498288307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388886664210034657537637 447916249539381498288307)
                  ·
                    rfl

theorem cell20_981353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_981353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981353 prefixEnd_981353 := by exact prefixLift 981353
  have htrace : WordTrace (prefixWord ++ tailWord_981353) baseStart_981353 baseEnd_981353 := by
    simpa [prefixWord, tailWord_981353, baseEnd_981353] using wordTrace_append hprefix tailTrace_981353
  have hstable : (prefixWord ++ tailWord_981353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981353).length < 2 ^ (prefixWord ++ tailWord_981353).sum := by decide
  have hdescent : baseEnd_981353 < baseStart_981353 := by decide
  rcases family_descends (prefixWord ++ tailWord_981353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981377 : List Nat := [1, 2, 4, 3, 1, 1, 8]
def baseStart_981377 : Nat := 118140960795 + 981377 * 2 ^ 59
def prefixEnd_981377 : Nat := 4983230072969 + 3 ^ 40 * 981377 * 2
def baseEnd_981377 : Nat := 49769689310371564609801

theorem tailTrace_981377 : CollatzResearch.WordTrace tailWord_981377 prefixEnd_981377 49769689310371564609801 := by
  unfold tailWord_981377
  simp only [CollatzResearch.WordTrace]
  refine ⟨35793759765646209692926385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23862506510430806461950923 35793759765646209692926385)
  ·
    refine ⟨26845319824234657269694789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35793759765646209692926385 26845319824234657269694789)
    ·
      refine ⟨5033497467043998238067773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26845319824234657269694789 5033497467043998238067773)
      ·
        refine ⟨1887561550141499339275415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5033497467043998238067773 1887561550141499339275415)
        ·
          refine ⟨2831342325212249008913123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887561550141499339275415 2831342325212249008913123)
          ·
            refine ⟨4247013487818373513369685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831342325212249008913123 4247013487818373513369685)
            ·
              refine ⟨49769689310371564609801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4247013487818373513369685 49769689310371564609801)
              ·
                rfl

theorem cell20_981377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 8].length) (baseStart_981377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981377 prefixEnd_981377 := by exact prefixLift 981377
  have htrace : WordTrace (prefixWord ++ tailWord_981377) baseStart_981377 baseEnd_981377 := by
    simpa [prefixWord, tailWord_981377, baseEnd_981377] using wordTrace_append hprefix tailTrace_981377
  have hstable : (prefixWord ++ tailWord_981377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981377).length < 2 ^ (prefixWord ++ tailWord_981377).sum := by decide
  have hdescent : baseEnd_981377 < baseStart_981377 := by decide
  rcases family_descends (prefixWord ++ tailWord_981377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981384 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_981384 : Nat := 118140960795 + 981384 * 2 ^ 59
def prefixEnd_981384 : Nat := 4983230072969 + 3 ^ 40 * 981384 * 2
def baseEnd_981384 : Nat := 447930398784083168254847

theorem tailTrace_981384 : CollatzResearch.WordTrace tailWord_981384 prefixEnd_981384 447930398784083168254847 := by
  unfold tailWord_981384
  simp only [CollatzResearch.WordTrace]
  refine ⟨17897007538310424944215603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23862676717747233258954137 17897007538310424944215603)
  ·
    refine ⟨26845511307465637416323405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17897007538310424944215603 26845511307465637416323405)
    ·
      refine ⟨10067066740299614031121277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26845511307465637416323405 10067066740299614031121277)
      ·
        refine ⟨3775150027612355261670479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10067066740299614031121277 3775150027612355261670479)
        ·
          refine ⟨5662725041418532892505719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775150027612355261670479 5662725041418532892505719)
          ·
            refine ⟨8494087562127799338758579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662725041418532892505719 8494087562127799338758579)
            ·
              refine ⟨12741131343191699008137869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8494087562127799338758579 12741131343191699008137869)
              ·
                refine ⟨4777924253696887128051701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12741131343191699008137869 4777924253696887128051701)
                ·
                  refine ⟨447930398784083168254847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4777924253696887128051701 447930398784083168254847)
                  ·
                    rfl

theorem cell20_981384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_981384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981384 prefixEnd_981384 := by exact prefixLift 981384
  have htrace : WordTrace (prefixWord ++ tailWord_981384) baseStart_981384 baseEnd_981384 := by
    simpa [prefixWord, tailWord_981384, baseEnd_981384] using wordTrace_append hprefix tailTrace_981384
  have hstable : (prefixWord ++ tailWord_981384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981384).length < 2 ^ (prefixWord ++ tailWord_981384).sum := by decide
  have hdescent : baseEnd_981384 < baseStart_981384 := by decide
  rcases family_descends (prefixWord ++ tailWord_981384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981415 : List Nat := [1, 1, 6, 1, 1, 2, 2, 6]
def baseStart_981415 : Nat := 118140960795 + 981415 * 2 ^ 59
def prefixEnd_981415 : Nat := 4983230072969 + 3 ^ 40 * 981415 * 2
def baseEnd_981415 : Nat := 149314849342928279407129

theorem tailTrace_981415 : CollatzResearch.WordTrace tailWord_981415 prefixEnd_981415 149314849342928279407129 := by
  unfold tailWord_981415
  simp only [CollatzResearch.WordTrace]
  refine ⟨35795145739508542182809699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23863430493005694788539799 35795145739508542182809699)
  ·
    refine ⟨53692718609262813274214549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35795145739508542182809699 53692718609262813274214549)
    ·
      refine ⟨2516846184809194372228807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53692718609262813274214549 2516846184809194372228807)
      ·
        refine ⟨3775269277213791558343211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516846184809194372228807 3775269277213791558343211)
        ·
          refine ⟨5662903915820687337514817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775269277213791558343211 5662903915820687337514817)
          ·
            refine ⟨4247177936865515503136113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5662903915820687337514817 4247177936865515503136113)
            ·
              refine ⟨3185383452649136627352085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4247177936865515503136113 3185383452649136627352085)
              ·
                refine ⟨149314849342928279407129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3185383452649136627352085 149314849342928279407129)
                ·
                  rfl

theorem cell20_981415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_981415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981415 prefixEnd_981415 := by exact prefixLift 981415
  have htrace : WordTrace (prefixWord ++ tailWord_981415) baseStart_981415 baseEnd_981415 := by
    simpa [prefixWord, tailWord_981415, baseEnd_981415] using wordTrace_append hprefix tailTrace_981415
  have hstable : (prefixWord ++ tailWord_981415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981415).length < 2 ^ (prefixWord ++ tailWord_981415).sum := by decide
  have hdescent : baseEnd_981415 < baseStart_981415 := by decide
  rcases family_descends (prefixWord ++ tailWord_981415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981498 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_981498 : Nat := 118140960795 + 981498 * 2 ^ 59
def prefixEnd_981498 : Nat := 4983230072969 + 3 ^ 40 * 981498 * 2
def baseEnd_981498 : Nat := 447982431490405438454381

theorem tailTrace_981498 : CollatzResearch.WordTrace tailWord_981498 prefixEnd_981498 447982431490405438454381 := by
  unfold tailWord_981498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8949543249551961839520287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23865448665471898238720765 8949543249551961839520287)
  ·
    refine ⟨13424314874327942759280431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8949543249551961839520287 13424314874327942759280431)
    ·
      refine ⟨20136472311491914138920647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13424314874327942759280431 20136472311491914138920647)
      ·
        refine ⟨30204708467237871208380971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20136472311491914138920647 30204708467237871208380971)
        ·
          refine ⟨45307062700856806812571457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30204708467237871208380971 45307062700856806812571457)
          ·
            refine ⟨33980297025642605109428593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45307062700856806812571457 33980297025642605109428593)
            ·
              refine ⟨25485222769231953832071445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33980297025642605109428593 25485222769231953832071445)
              ·
                refine ⟨1194619817307747835878349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25485222769231953832071445 1194619817307747835878349)
                ·
                  refine ⟨447982431490405438454381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194619817307747835878349 447982431490405438454381)
                  ·
                    rfl

theorem cell20_981498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_981498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981498 prefixEnd_981498 := by exact prefixLift 981498
  have htrace : WordTrace (prefixWord ++ tailWord_981498) baseStart_981498 baseEnd_981498 := by
    simpa [prefixWord, tailWord_981498, baseEnd_981498] using wordTrace_append hprefix tailTrace_981498
  have hstable : (prefixWord ++ tailWord_981498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981498).length < 2 ^ (prefixWord ++ tailWord_981498).sum := by decide
  have hdescent : baseEnd_981498 < baseStart_981498 := by decide
  rcases family_descends (prefixWord ++ tailWord_981498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981512 : List Nat := [2, 1, 3, 2, 1, 1, 1, 9]
def baseStart_981512 : Nat := 118140960795 + 981512 * 2 ^ 59
def prefixEnd_981512 : Nat := 4983230072969 + 3 ^ 40 * 981512 * 2
def baseEnd_981512 : Nat := 149329607157294537329219

theorem tailTrace_981512 : CollatzResearch.WordTrace tailWord_981512 prefixEnd_981512 149329607157294537329219 := by
  unfold tailWord_981512
  simp only [CollatzResearch.WordTrace]
  refine ⟨17899341810078563874545395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23865789080104751832727193 17899341810078563874545395)
  ·
    refine ⟨26849012715117845811818093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17899341810078563874545395 26849012715117845811818093)
    ·
      refine ⟨10068379768169192179431785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26849012715117845811818093 10068379768169192179431785)
      ·
        refine ⟨7551284826126894134573839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10068379768169192179431785 7551284826126894134573839)
        ·
          refine ⟨11326927239190341201860759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7551284826126894134573839 11326927239190341201860759)
          ·
            refine ⟨16990390858785511802791139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11326927239190341201860759 16990390858785511802791139)
            ·
              refine ⟨25485586288178267704186709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16990390858785511802791139 25485586288178267704186709)
              ·
                refine ⟨149329607157294537329219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25485586288178267704186709 149329607157294537329219)
                ·
                  rfl

theorem cell20_981512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_981512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981512 prefixEnd_981512 := by exact prefixLift 981512
  have htrace : WordTrace (prefixWord ++ tailWord_981512) baseStart_981512 baseEnd_981512 := by
    simpa [prefixWord, tailWord_981512, baseEnd_981512] using wordTrace_append hprefix tailTrace_981512
  have hstable : (prefixWord ++ tailWord_981512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981512).length < 2 ^ (prefixWord ++ tailWord_981512).sum := by decide
  have hdescent : baseEnd_981512 < baseStart_981512 := by decide
  rcases family_descends (prefixWord ++ tailWord_981512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981519 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_981519 : Nat := 118140960795 + 981519 * 2 ^ 59
def prefixEnd_981519 : Nat := 4983230072969 + 3 ^ 40 * 981519 * 2
def baseEnd_981519 : Nat := 447992016462622698754295

theorem tailTrace_981519 : CollatzResearch.WordTrace tailWord_981519 prefixEnd_981519 447992016462622698754295 := by
  unfold tailWord_981519
  simp only [CollatzResearch.WordTrace]
  refine ⟨35798938931131767944595611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23865959287421178629730407 35798938931131767944595611)
  ·
    refine ⟨53698408396697651916893417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35798938931131767944595611 53698408396697651916893417)
    ·
      refine ⟨40273806297523238937670063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53698408396697651916893417 40273806297523238937670063)
      ·
        refine ⟨60410709446284858406505095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40273806297523238937670063 60410709446284858406505095)
        ·
          refine ⟨90616064169427287609757643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60410709446284858406505095 90616064169427287609757643)
          ·
            refine ⟨135924096254140931414636465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90616064169427287609757643 135924096254140931414636465)
            ·
              refine ⟨101943072190605698560977349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135924096254140931414636465 101943072190605698560977349)
              ·
                refine ⟨19114326035738568480183253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101943072190605698560977349 19114326035738568480183253)
                ·
                  refine ⟨447992016462622698754295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19114326035738568480183253 447992016462622698754295)
                  ·
                    rfl

theorem cell20_981519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_981519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981519 prefixEnd_981519 := by exact prefixLift 981519
  have htrace : WordTrace (prefixWord ++ tailWord_981519) baseStart_981519 baseEnd_981519 := by
    simpa [prefixWord, tailWord_981519, baseEnd_981519] using wordTrace_append hprefix tailTrace_981519
  have hstable : (prefixWord ++ tailWord_981519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981519).length < 2 ^ (prefixWord ++ tailWord_981519).sum := by decide
  have hdescent : baseEnd_981519 < baseStart_981519 := by decide
  rcases family_descends (prefixWord ++ tailWord_981519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981539 : List Nat := [1, 1, 1, 4, 4, 1, 3, 3, 2]
def baseStart_981539 : Nat := 118140960795 + 981539 * 2 ^ 59
def prefixEnd_981539 : Nat := 4983230072969 + 3 ^ 40 * 981539 * 2
def baseEnd_981539 : Nat := 448001145007591518087547

theorem tailTrace_981539 : CollatzResearch.WordTrace tailWord_981539 prefixEnd_981539 448001145007591518087547 := by
  unfold tailWord_981539
  simp only [CollatzResearch.WordTrace]
  refine ⟨35799668391059311360323671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23866445594039540906882447 35799668391059311360323671)
  ·
    refine ⟨53699502586588967040485507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35799668391059311360323671 53699502586588967040485507)
    ·
      refine ⟨80549253879883450560728261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53699502586588967040485507 80549253879883450560728261)
      ·
        refine ⟨15102985102478146980136549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80549253879883450560728261 15102985102478146980136549)
        ·
          refine ⟨2831809706714652558775603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15102985102478146980136549 2831809706714652558775603)
          ·
            refine ⟨4247714560071978838163405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831809706714652558775603 4247714560071978838163405)
            ·
              refine ⟨1592892960026992064311277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4247714560071978838163405 1592892960026992064311277)
              ·
                refine ⟨597334860010122024116729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1592892960026992064311277 597334860010122024116729)
                ·
                  refine ⟨448001145007591518087547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597334860010122024116729 448001145007591518087547)
                  ·
                    rfl

theorem cell20_981539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 2].length) (baseStart_981539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981539 prefixEnd_981539 := by exact prefixLift 981539
  have htrace : WordTrace (prefixWord ++ tailWord_981539) baseStart_981539 baseEnd_981539 := by
    simpa [prefixWord, tailWord_981539, baseEnd_981539] using wordTrace_append hprefix tailTrace_981539
  have hstable : (prefixWord ++ tailWord_981539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981539).length < 2 ^ (prefixWord ++ tailWord_981539).sum := by decide
  have hdescent : baseEnd_981539 < baseStart_981539 := by decide
  rcases family_descends (prefixWord ++ tailWord_981539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981566 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_981566 : Nat := 118140960795 + 981566 * 2 ^ 59
def prefixEnd_981566 : Nat := 4983230072969 + 3 ^ 40 * 981566 * 2
def baseEnd_981566 : Nat := 448013468543299424187437

theorem tailTrace_981566 : CollatzResearch.WordTrace tailWord_981566 prefixEnd_981566 448013468543299424187437 := by
  unfold tailWord_981566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475081645245186871444569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23867102107974329981037701 4475081645245186871444569)
  ·
    refine ⟨3356311233933890153583427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4475081645245186871444569 3356311233933890153583427)
    ·
      refine ⟨5034466850900835230375141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356311233933890153583427 5034466850900835230375141)
      ·
        refine ⟨943962534543906605695339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5034466850900835230375141 943962534543906605695339)
        ·
          refine ⟨1415943801815859908543009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943962534543906605695339 1415943801815859908543009)
          ·
            refine ⟨1061957851361894931407257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1415943801815859908543009 1061957851361894931407257)
            ·
              refine ⟨796468388521421198555443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061957851361894931407257 796468388521421198555443)
              ·
                refine ⟨1194702582782131797833165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796468388521421198555443 1194702582782131797833165)
                ·
                  refine ⟨448013468543299424187437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194702582782131797833165 448013468543299424187437)
                  ·
                    rfl

theorem cell20_981566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_981566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981566 prefixEnd_981566 := by exact prefixLift 981566
  have htrace : WordTrace (prefixWord ++ tailWord_981566) baseStart_981566 baseEnd_981566 := by
    simpa [prefixWord, tailWord_981566, baseEnd_981566] using wordTrace_append hprefix tailTrace_981566
  have hstable : (prefixWord ++ tailWord_981566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981566).length < 2 ^ (prefixWord ++ tailWord_981566).sum := by decide
  have hdescent : baseEnd_981566 < baseStart_981566 := by decide
  rcases family_descends (prefixWord ++ tailWord_981566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981605 : List Nat := [1, 3, 1, 3, 5, 7]
def baseStart_981605 : Nat := 118140960795 + 981605 * 2 ^ 59
def prefixEnd_981605 : Nat := 4983230072969 + 3 ^ 40 * 981605 * 2
def baseEnd_981605 : Nat := 16593750711332911921751

theorem tailTrace_981605 : CollatzResearch.WordTrace tailWord_981605 prefixEnd_981605 16593750711332911921751 := by
  unfold tailWord_981605
  simp only [CollatzResearch.WordTrace]
  refine ⟨35802075608820204632226269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23868050405880136421484179 35802075608820204632226269)
  ·
    refine ⟨13425778353307576737084851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35802075608820204632226269 13425778353307576737084851)
    ·
      refine ⟨20138667529961365105627277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13425778353307576737084851 20138667529961365105627277)
      ·
        refine ⟨7552000323735511914610229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20138667529961365105627277 7552000323735511914610229)
        ·
          refine ⟨708000030350204241994709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7552000323735511914610229 708000030350204241994709)
          ·
            refine ⟨16593750711332911921751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 708000030350204241994709 16593750711332911921751)
            ·
              rfl

theorem cell20_981605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 7].length) (baseStart_981605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981605 prefixEnd_981605 := by exact prefixLift 981605
  have htrace : WordTrace (prefixWord ++ tailWord_981605) baseStart_981605 baseEnd_981605 := by
    simpa [prefixWord, tailWord_981605, baseEnd_981605] using wordTrace_append hprefix tailTrace_981605
  have hstable : (prefixWord ++ tailWord_981605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981605).length < 2 ^ (prefixWord ++ tailWord_981605).sum := by decide
  have hdescent : baseEnd_981605 < baseStart_981605 := by decide
  rcases family_descends (prefixWord ++ tailWord_981605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981608 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 3]
def baseStart_981608 : Nat := 118140960795 + 981608 * 2 ^ 59
def prefixEnd_981608 : Nat := 4983230072969 + 3 ^ 40 * 981608 * 2
def baseEnd_981608 : Nat := 448032638487733944787265

theorem tailTrace_981608 : CollatzResearch.WordTrace tailWord_981608 prefixEnd_981608 448032638487733944787265 := by
  unfold tailWord_981608
  simp only [CollatzResearch.WordTrace]
  refine ⟨17901092513904668072292739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23868123351872890763056985 17901092513904668072292739)
  ·
    refine ⟨26851638770857002108439109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17901092513904668072292739 26851638770857002108439109)
    ·
      refine ⟨5034682269535687895332333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26851638770857002108439109 5034682269535687895332333)
      ·
        refine ⟨1888005851075882960749625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5034682269535687895332333 1888005851075882960749625)
        ·
          refine ⟨1416004388306912220562219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1888005851075882960749625 1416004388306912220562219)
          ·
            refine ⟨2124006582460368330843329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416004388306912220562219 2124006582460368330843329)
            ·
              refine ⟨1593004936845276248132497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2124006582460368330843329 1593004936845276248132497)
              ·
                refine ⟨1194753702633957186099373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593004936845276248132497 1194753702633957186099373)
                ·
                  refine ⟨448032638487733944787265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194753702633957186099373 448032638487733944787265)
                  ·
                    rfl

theorem cell20_981608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_981608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981608 prefixEnd_981608 := by exact prefixLift 981608
  have htrace : WordTrace (prefixWord ++ tailWord_981608) baseStart_981608 baseEnd_981608 := by
    simpa [prefixWord, tailWord_981608, baseEnd_981608] using wordTrace_append hprefix tailTrace_981608
  have hstable : (prefixWord ++ tailWord_981608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981608).length < 2 ^ (prefixWord ++ tailWord_981608).sum := by decide
  have hdescent : baseEnd_981608 < baseStart_981608 := by decide
  rcases family_descends (prefixWord ++ tailWord_981608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981612 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 3]
def baseStart_981612 : Nat := 118140960795 + 981612 * 2 ^ 59
def prefixEnd_981612 : Nat := 4983230072969 + 3 ^ 40 * 981612 * 2
def baseEnd_981612 : Nat := 448034464196727708653915

theorem tailTrace_981612 : CollatzResearch.WordTrace tailWord_981612 prefixEnd_981612 448034464196727708653915 := by
  unfold tailWord_981612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17901165459897422413865545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23868220613196563218487393 17901165459897422413865545)
  ·
    refine ⟨13425874094923066810399159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17901165459897422413865545 13425874094923066810399159)
    ·
      refine ⟨20138811142384600215598739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13425874094923066810399159 20138811142384600215598739)
      ·
        refine ⟨30208216713576900323398109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20138811142384600215598739 30208216713576900323398109)
        ·
          refine ⟨11328081267591337621274291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30208216713576900323398109 11328081267591337621274291)
          ·
            refine ⟨16992121901387006431911437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11328081267591337621274291 16992121901387006431911437)
            ·
              refine ⟨6372045713020127411966789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16992121901387006431911437 6372045713020127411966789)
              ·
                refine ⟨1194758571191273889743773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6372045713020127411966789 1194758571191273889743773)
                ·
                  refine ⟨448034464196727708653915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194758571191273889743773 448034464196727708653915)
                  ·
                    rfl

theorem cell20_981612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_981612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981612 prefixEnd_981612 := by exact prefixLift 981612
  have htrace : WordTrace (prefixWord ++ tailWord_981612) baseStart_981612 baseEnd_981612 := by
    simpa [prefixWord, tailWord_981612, baseEnd_981612] using wordTrace_append hprefix tailTrace_981612
  have hstable : (prefixWord ++ tailWord_981612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981612).length < 2 ^ (prefixWord ++ tailWord_981612).sum := by decide
  have hdescent : baseEnd_981612 < baseStart_981612 := by decide
  rcases family_descends (prefixWord ++ tailWord_981612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981615 : List Nat := [1, 1, 2, 1, 3, 2, 6, 2, 2]
def baseStart_981615 : Nat := 118140960795 + 981615 * 2 ^ 59
def prefixEnd_981615 : Nat := 4983230072969 + 3 ^ 40 * 981615 * 2
def baseEnd_981615 : Nat := 448035833478473031553903

theorem tailTrace_981615 : CollatzResearch.WordTrace tailWord_981615 prefixEnd_981615 448035833478473031553903 := by
  unfold tailWord_981615
  simp only [CollatzResearch.WordTrace]
  refine ⟨35802440338783976340090299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23868293559189317560060199 35802440338783976340090299)
  ·
    refine ⟨53703660508175964510135449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35802440338783976340090299 53703660508175964510135449)
    ·
      refine ⟨40277745381131973382601587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53703660508175964510135449 40277745381131973382601587)
      ·
        refine ⟨60416618071697960073902381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40277745381131973382601587 60416618071697960073902381)
        ·
          refine ⟨22656231776886735027713393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60416618071697960073902381 22656231776886735027713393)
          ·
            refine ⟨16992173832665051270785045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22656231776886735027713393 16992173832665051270785045)
            ·
              refine ⟨796508148406174278318049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16992173832665051270785045 796508148406174278318049)
              ·
                refine ⟨597381111304630708738537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796508148406174278318049 597381111304630708738537)
                ·
                  refine ⟨448035833478473031553903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597381111304630708738537 448035833478473031553903)
                  ·
                    rfl

theorem cell20_981615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 2].length) (baseStart_981615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981615 prefixEnd_981615 := by exact prefixLift 981615
  have htrace : WordTrace (prefixWord ++ tailWord_981615) baseStart_981615 baseEnd_981615 := by
    simpa [prefixWord, tailWord_981615, baseEnd_981615] using wordTrace_append hprefix tailTrace_981615
  have hstable : (prefixWord ++ tailWord_981615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981615).length < 2 ^ (prefixWord ++ tailWord_981615).sum := by decide
  have hdescent : baseEnd_981615 < baseStart_981615 := by decide
  rcases family_descends (prefixWord ++ tailWord_981615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981636 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_981636 : Nat := 118140960795 + 981636 * 2 ^ 59
def prefixEnd_981636 : Nat := 4983230072969 + 3 ^ 40 * 981636 * 2
def baseEnd_981636 : Nat := 448045418450690291853817

theorem tailTrace_981636 : CollatzResearch.WordTrace tailWord_981636 prefixEnd_981636 448045418450690291853817 := by
  unfold tailWord_981636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17901603135853948463302381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23868804181138597951069841 17901603135853948463302381)
  ·
    refine ⟨6713101175945230673738393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17901603135853948463302381 6713101175945230673738393)
    ·
      refine ⟨5034825881958923005303795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6713101175945230673738393 5034825881958923005303795)
      ·
        refine ⟨7552238822938384507955693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5034825881958923005303795 7552238822938384507955693)
        ·
          refine ⟨2832089558601894190483385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7552238822938384507955693 2832089558601894190483385)
          ·
            refine ⟨2124067168951420642862539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2832089558601894190483385 2124067168951420642862539)
            ·
              refine ⟨3186100753427130964293809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124067168951420642862539 3186100753427130964293809)
              ·
                refine ⟨2389575565070348223220357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186100753427130964293809 2389575565070348223220357)
                ·
                  refine ⟨448045418450690291853817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2389575565070348223220357 448045418450690291853817)
                  ·
                    rfl

theorem cell20_981636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_981636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981636 prefixEnd_981636 := by exact prefixLift 981636
  have htrace : WordTrace (prefixWord ++ tailWord_981636) baseStart_981636 baseEnd_981636 := by
    simpa [prefixWord, tailWord_981636, baseEnd_981636] using wordTrace_append hprefix tailTrace_981636
  have hstable : (prefixWord ++ tailWord_981636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981636).length < 2 ^ (prefixWord ++ tailWord_981636).sum := by decide
  have hdescent : baseEnd_981636 < baseStart_981636 := by decide
  rcases family_descends (prefixWord ++ tailWord_981636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981695 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_981695 : Nat := 118140960795 + 981695 * 2 ^ 59
def prefixEnd_981695 : Nat := 4983230072969 + 3 ^ 40 * 981695 * 2
def baseEnd_981695 : Nat := 448072347658348308886909

theorem tailTrace_981695 : CollatzResearch.WordTrace tailWord_981695 prefixEnd_981695 448072347658348308886909 := by
  unfold tailWord_981695
  simp only [CollatzResearch.WordTrace]
  refine ⟨35805358178494150003002539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23870238785662766668668359 35805358178494150003002539)
  ·
    refine ⟨53708037267741225004503809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35805358178494150003002539 53708037267741225004503809)
    ·
      refine ⟨40281027950805918753377857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53708037267741225004503809 40281027950805918753377857)
      ·
        refine ⟨30210770963104439065033393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40281027950805918753377857 30210770963104439065033393)
        ·
          refine ⟨22658078222328329298775045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30210770963104439065033393 22658078222328329298775045)
          ·
            refine ⟨4248389666686561743520321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22658078222328329298775045 4248389666686561743520321)
            ·
              refine ⟨3186292250014921307640241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4248389666686561743520321 3186292250014921307640241)
              ·
                refine ⟨2389719187511190980730181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186292250014921307640241 2389719187511190980730181)
                ·
                  refine ⟨448072347658348308886909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2389719187511190980730181 448072347658348308886909)
                  ·
                    rfl

theorem cell20_981695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_981695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981695 prefixEnd_981695 := by exact prefixLift 981695
  have htrace : WordTrace (prefixWord ++ tailWord_981695) baseStart_981695 baseEnd_981695 := by
    simpa [prefixWord, tailWord_981695, baseEnd_981695] using wordTrace_append hprefix tailTrace_981695
  have hstable : (prefixWord ++ tailWord_981695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981695).length < 2 ^ (prefixWord ++ tailWord_981695).sum := by decide
  have hdescent : baseEnd_981695 < baseStart_981695 := by decide
  rcases family_descends (prefixWord ++ tailWord_981695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981708 : List Nat := [2, 2, 1, 5, 1, 3, 1, 3, 2]
def baseStart_981708 : Nat := 118140960795 + 981708 * 2 ^ 59
def prefixEnd_981708 : Nat := 4983230072969 + 3 ^ 40 * 981708 * 2
def baseEnd_981708 : Nat := 448078281212578041453523

theorem tailTrace_981708 : CollatzResearch.WordTrace tailWord_981708 prefixEnd_981708 448078281212578041453523 := by
  unfold tailWord_981708
  simp only [CollatzResearch.WordTrace]
  refine ⟨17902916163723526611612889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23870554884964702148817185 17902916163723526611612889)
  ·
    refine ⟨13427187122792644958709667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17902916163723526611612889 13427187122792644958709667)
    ·
      refine ⟨20140780684188967438064501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13427187122792644958709667 20140780684188967438064501)
      ·
        refine ⟨1888198189142715697318547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20140780684188967438064501 1888198189142715697318547)
        ·
          refine ⟨2832297283714073545977821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888198189142715697318547 2832297283714073545977821)
          ·
            refine ⟨1062111481392777579741683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2832297283714073545977821 1062111481392777579741683)
            ·
              refine ⟨1593167222089166369612525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062111481392777579741683 1593167222089166369612525)
              ·
                refine ⟨597437708283437388604697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593167222089166369612525 597437708283437388604697)
                ·
                  refine ⟨448078281212578041453523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597437708283437388604697 448078281212578041453523)
                  ·
                    rfl

theorem cell20_981708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_981708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981708 prefixEnd_981708 := by exact prefixLift 981708
  have htrace : WordTrace (prefixWord ++ tailWord_981708) baseStart_981708 baseEnd_981708 := by
    simpa [prefixWord, tailWord_981708, baseEnd_981708] using wordTrace_append hprefix tailTrace_981708
  have hstable : (prefixWord ++ tailWord_981708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981708).length < 2 ^ (prefixWord ++ tailWord_981708).sum := by decide
  have hdescent : baseEnd_981708 < baseStart_981708 := by decide
  rcases family_descends (prefixWord ++ tailWord_981708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981743 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 3]
def baseStart_981743 : Nat := 118140960795 + 981743 * 2 ^ 59
def prefixEnd_981743 : Nat := 4983230072969 + 3 ^ 40 * 981743 * 2
def baseEnd_981743 : Nat := 448094256166273475286713

theorem tailTrace_981743 : CollatzResearch.WordTrace tailWord_981743 prefixEnd_981743 448094256166273475286713 := by
  unfold tailWord_981743
  simp only [CollatzResearch.WordTrace]
  refine ⟨35807108882320254200749883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23871405921546836133833255 35807108882320254200749883)
  ·
    refine ⟨53710663323480381301124825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35807108882320254200749883 53710663323480381301124825)
    ·
      refine ⟨40282997492610285975843619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53710663323480381301124825 40282997492610285975843619)
      ·
        refine ⟨60424496238915428963765429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40282997492610285975843619 60424496238915428963765429)
        ·
          refine ⟨5664796522398321465353009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60424496238915428963765429 5664796522398321465353009)
          ·
            refine ⟨4248597391798741099014757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5664796522398321465353009 4248597391798741099014757)
            ·
              refine ⟨796612010962263956065267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4248597391798741099014757 796612010962263956065267)
              ·
                refine ⟨1194918016443395934097901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796612010962263956065267 1194918016443395934097901)
                ·
                  refine ⟨448094256166273475286713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194918016443395934097901 448094256166273475286713)
                  ·
                    rfl

theorem cell20_981743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 3].length) (baseStart_981743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981743 prefixEnd_981743 := by exact prefixLift 981743
  have htrace : WordTrace (prefixWord ++ tailWord_981743) baseStart_981743 baseEnd_981743 := by
    simpa [prefixWord, tailWord_981743, baseEnd_981743] using wordTrace_append hprefix tailTrace_981743
  have hstable : (prefixWord ++ tailWord_981743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981743).length < 2 ^ (prefixWord ++ tailWord_981743).sum := by decide
  have hdescent : baseEnd_981743 < baseStart_981743 := by decide
  rcases family_descends (prefixWord ++ tailWord_981743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981809 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_981809 : Nat := 118140960795 + 981809 * 2 ^ 59
def prefixEnd_981809 : Nat := 4983230072969 + 3 ^ 40 * 981809 * 2
def baseEnd_981809 : Nat := 448124380364670579086443

theorem tailTrace_981809 : CollatzResearch.WordTrace tailWord_981809 prefixEnd_981809 448124380364670579086443 := by
  unfold tailWord_981809
  simp only [CollatzResearch.WordTrace]
  refine ⟨35809516100081147472652481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23873010733387431648434987 35809516100081147472652481)
  ·
    refine ⟨26857137075060860604489361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35809516100081147472652481 26857137075060860604489361)
    ·
      refine ⟨20142852806295645453367021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26857137075060860604489361 20142852806295645453367021)
      ·
        refine ⟨7553569802360867045012633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20142852806295645453367021 7553569802360867045012633)
        ·
          refine ⟨5665177351770650283759475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7553569802360867045012633 5665177351770650283759475)
          ·
            refine ⟨8497766027655975425639213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5665177351770650283759475 8497766027655975425639213)
            ·
              refine ⟨3186662260370990784614705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8497766027655975425639213 3186662260370990784614705)
              ·
                refine ⟨2389996695278243088461029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186662260370990784614705 2389996695278243088461029)
                ·
                  refine ⟨448124380364670579086443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2389996695278243088461029 448124380364670579086443)
                  ·
                    rfl

theorem cell20_981809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_981809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981809 prefixEnd_981809 := by exact prefixLift 981809
  have htrace : WordTrace (prefixWord ++ tailWord_981809) baseStart_981809 baseEnd_981809 := by
    simpa [prefixWord, tailWord_981809, baseEnd_981809] using wordTrace_append hprefix tailTrace_981809
  have hstable : (prefixWord ++ tailWord_981809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981809).length < 2 ^ (prefixWord ++ tailWord_981809).sum := by decide
  have hdescent : baseEnd_981809 < baseStart_981809 := by decide
  rcases family_descends (prefixWord ++ tailWord_981809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981822 : List Nat := [4, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_981822 : Nat := 118140960795 + 981822 * 2 ^ 59
def prefixEnd_981822 : Nat := 4983230072969 + 3 ^ 40 * 981822 * 2
def baseEnd_981822 : Nat := 448130313918900311653057

theorem tailTrace_981822 : CollatzResearch.WordTrace tailWord_981822 prefixEnd_981822 448130313918900311653057 := by
  unfold tailWord_981822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476248781129256336609465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23873326832689367128583813 4476248781129256336609465)
  ·
    refine ⟨3357186585846942252457099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4476248781129256336609465 3357186585846942252457099)
    ·
      refine ⟨5035779878770413378685649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3357186585846942252457099 5035779878770413378685649)
      ·
        refine ⟨3776834909077810034014237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5035779878770413378685649 3776834909077810034014237)
        ·
          refine ⟨1416313090904178762755339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3776834909077810034014237 1416313090904178762755339)
          ·
            refine ⟨2124469636356268144133009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416313090904178762755339 2124469636356268144133009)
            ·
              refine ⟨1593352227267201108099757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2124469636356268144133009 1593352227267201108099757)
              ·
                refine ⟨597507085225200415537409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593352227267201108099757 597507085225200415537409)
                ·
                  refine ⟨448130313918900311653057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597507085225200415537409 448130313918900311653057)
                  ·
                    rfl

theorem cell20_981822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_981822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981822 prefixEnd_981822 := by exact prefixLift 981822
  have htrace : WordTrace (prefixWord ++ tailWord_981822) baseStart_981822 baseEnd_981822 := by
    simpa [prefixWord, tailWord_981822, baseEnd_981822] using wordTrace_append hprefix tailTrace_981822
  have hstable : (prefixWord ++ tailWord_981822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981822).length < 2 ^ (prefixWord ++ tailWord_981822).sum := by decide
  have hdescent : baseEnd_981822 < baseStart_981822 := by decide
  rcases family_descends (prefixWord ++ tailWord_981822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981840 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 3]
def baseStart_981840 : Nat := 118140960795 + 981840 * 2 ^ 59
def prefixEnd_981840 : Nat := 4983230072969 + 3 ^ 40 * 981840 * 2
def baseEnd_981840 : Nat := 448138529609372249052983

theorem tailTrace_981840 : CollatzResearch.WordTrace tailWord_981840 prefixEnd_981840 448138529609372249052983 := by
  unfold tailWord_981840
  simp only [CollatzResearch.WordTrace]
  refine ⟨17905323381484419883515487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23873764508645893178020649 17905323381484419883515487)
  ·
    refine ⟨26857985072226629825273231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17905323381484419883515487 26857985072226629825273231)
    ·
      refine ⟨40286977608339944737909847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26857985072226629825273231 40286977608339944737909847)
      ·
        refine ⟨60430466412509917106864771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40286977608339944737909847 60430466412509917106864771)
        ·
          refine ⟨90645699618764875660297157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60430466412509917106864771 90645699618764875660297157)
          ·
            refine ⟨16996068678518414186305717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90645699618764875660297157 16996068678518414186305717)
            ·
              refine ⟨1593381438611101329966161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16996068678518414186305717 1593381438611101329966161)
              ·
                refine ⟨1195036078958325997474621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593381438611101329966161 1195036078958325997474621)
                ·
                  refine ⟨448138529609372249052983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195036078958325997474621 448138529609372249052983)
                  ·
                    rfl

theorem cell20_981840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_981840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981840 prefixEnd_981840 := by exact prefixLift 981840
  have htrace : WordTrace (prefixWord ++ tailWord_981840) baseStart_981840 baseEnd_981840 := by
    simpa [prefixWord, tailWord_981840, baseEnd_981840] using wordTrace_append hprefix tailTrace_981840
  have hstable : (prefixWord ++ tailWord_981840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981840).length < 2 ^ (prefixWord ++ tailWord_981840).sum := by decide
  have hdescent : baseEnd_981840 < baseStart_981840 := by decide
  rcases family_descends (prefixWord ++ tailWord_981840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981847 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_981847 : Nat := 118140960795 + 981847 * 2 ^ 59
def prefixEnd_981847 : Nat := 4983230072969 + 3 ^ 40 * 981847 * 2
def baseEnd_981847 : Nat := 448141724600111335819621

theorem tailTrace_981847 : CollatzResearch.WordTrace tailWord_981847 prefixEnd_981847 448141724600111335819621 := by
  unfold tailWord_981847
  simp only [CollatzResearch.WordTrace]
  refine ⟨35810902073943479962535795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23873934715962319975023863 35810902073943479962535795)
  ·
    refine ⟨53716353110915219943803693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35810902073943479962535795 53716353110915219943803693)
    ·
      refine ⟨20143632416593207478926385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53716353110915219943803693 20143632416593207478926385)
      ·
        refine ⟨15107724312444905609194789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20143632416593207478926385 15107724312444905609194789)
        ·
          refine ⟨2832698308583419801724023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15107724312444905609194789 2832698308583419801724023)
          ·
            refine ⟨4249047462875129702586035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832698308583419801724023 4249047462875129702586035)
            ·
              refine ⟨6373571194312694553879053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249047462875129702586035 6373571194312694553879053)
              ·
                refine ⟨2390089197867260457704645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6373571194312694553879053 2390089197867260457704645)
                ·
                  refine ⟨448141724600111335819621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2390089197867260457704645 448141724600111335819621)
                  ·
                    rfl

theorem cell20_981847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_981847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981847 prefixEnd_981847 := by exact prefixLift 981847
  have htrace : WordTrace (prefixWord ++ tailWord_981847) baseStart_981847 baseEnd_981847 := by
    simpa [prefixWord, tailWord_981847, baseEnd_981847] using wordTrace_append hprefix tailTrace_981847
  have hstable : (prefixWord ++ tailWord_981847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981847).length < 2 ^ (prefixWord ++ tailWord_981847).sum := by decide
  have hdescent : baseEnd_981847 < baseStart_981847 := by decide
  rcases family_descends (prefixWord ++ tailWord_981847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981881 : List Nat := [1, 2, 1, 3, 2, 5, 1, 3, 2]
def baseStart_981881 : Nat := 118140960795 + 981881 * 2 ^ 59
def prefixEnd_981881 : Nat := 4983230072969 + 3 ^ 40 * 981881 * 2
def baseEnd_981881 : Nat := 448157243126558328686149

theorem tailTrace_981881 : CollatzResearch.WordTrace tailWord_981881 prefixEnd_981881 448157243126558328686149 := by
  unfold tailWord_981881
  simp only [CollatzResearch.WordTrace]
  refine ⟨35812142155820303769273497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23874761437213535846182331 35812142155820303769273497)
  ·
    refine ⟨26859106616865227826955123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35812142155820303769273497 26859106616865227826955123)
    ·
      refine ⟨40288659925297841740432685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26859106616865227826955123 40288659925297841740432685)
      ·
        refine ⟨15108247471986690652662257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40288659925297841740432685 15108247471986690652662257)
        ·
          refine ⟨11331185603990017989496693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15108247471986690652662257 11331185603990017989496693)
          ·
            refine ⟨1062298650374064186515315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11331185603990017989496693 1062298650374064186515315)
            ·
              refine ⟨1593447975561096279772973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062298650374064186515315 1593447975561096279772973)
              ·
                refine ⟨597542990835411104914865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593447975561096279772973 597542990835411104914865)
                ·
                  refine ⟨448157243126558328686149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597542990835411104914865 448157243126558328686149)
                  ·
                    rfl

theorem cell20_981881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_981881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981881 prefixEnd_981881 := by exact prefixLift 981881
  have htrace : WordTrace (prefixWord ++ tailWord_981881) baseStart_981881 baseEnd_981881 := by
    simpa [prefixWord, tailWord_981881, baseEnd_981881] using wordTrace_append hprefix tailTrace_981881
  have hstable : (prefixWord ++ tailWord_981881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981881).length < 2 ^ (prefixWord ++ tailWord_981881).sum := by decide
  have hdescent : baseEnd_981881 < baseStart_981881 := by decide
  rcases family_descends (prefixWord ++ tailWord_981881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981898 : List Nat := [3, 1, 2, 4, 1, 2, 3, 2, 2]
def baseStart_981898 : Nat := 118140960795 + 981898 * 2 ^ 59
def prefixEnd_981898 : Nat := 4983230072969 + 3 ^ 40 * 981898 * 2
def baseEnd_981898 : Nat := 448165002389781825119413

theorem tailTrace_981898 : CollatzResearch.WordTrace tailWord_981898 prefixEnd_981898 448165002389781825119413 := by
  unfold tailWord_981898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8953190549189678918160587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23875174797839143781761565 8953190549189678918160587)
  ·
    refine ⟨13429785823784518377240881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8953190549189678918160587 13429785823784518377240881)
    ·
      refine ⟨10072339367838388782930661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13429785823784518377240881 10072339367838388782930661)
      ·
        refine ⟨1888563631469697896799499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10072339367838388782930661 1888563631469697896799499)
        ·
          refine ⟨2832845447204546845199249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888563631469697896799499 2832845447204546845199249)
          ·
            refine ⟨2124634085403410133899437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2832845447204546845199249 2124634085403410133899437)
            ·
              refine ⟨796737782026278800212289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2124634085403410133899437 796737782026278800212289)
              ·
                refine ⟨597553336519709100159217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796737782026278800212289 597553336519709100159217)
                ·
                  refine ⟨448165002389781825119413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597553336519709100159217 448165002389781825119413)
                  ·
                    rfl

theorem cell20_981898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_981898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981898 prefixEnd_981898 := by exact prefixLift 981898
  have htrace : WordTrace (prefixWord ++ tailWord_981898) baseStart_981898 baseEnd_981898 := by
    simpa [prefixWord, tailWord_981898, baseEnd_981898] using wordTrace_append hprefix tailTrace_981898
  have hstable : (prefixWord ++ tailWord_981898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981898).length < 2 ^ (prefixWord ++ tailWord_981898).sum := by decide
  have hdescent : baseEnd_981898 < baseStart_981898 := by decide
  rcases family_descends (prefixWord ++ tailWord_981898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981899 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_981899 : Nat := 118140960795 + 981899 * 2 ^ 59
def prefixEnd_981899 : Nat := 4983230072969 + 3 ^ 40 * 981899 * 2
def baseEnd_981899 : Nat := 448165458817030266086075

theorem tailTrace_981899 : CollatzResearch.WordTrace tailWord_981899 prefixEnd_981899 448165458817030266086075 := by
  unfold tailWord_981899
  simp only [CollatzResearch.WordTrace]
  refine ⟨35812798669755092843428751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23875199113170061895619167 35812798669755092843428751)
  ·
    refine ⟨53719198004632639265143127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35812798669755092843428751 53719198004632639265143127)
    ·
      refine ⟨80578797006948958897714691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53719198004632639265143127 80578797006948958897714691)
      ·
        refine ⟨120868195510423438346572037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80578797006948958897714691 120868195510423438346572037)
        ·
          refine ⟨22662786658204394689982257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120868195510423438346572037 22662786658204394689982257)
          ·
            refine ⟨16997089993653296017486693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22662786658204394689982257 16997089993653296017486693)
            ·
              refine ⟨3186954373809993003278755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16997089993653296017486693 3186954373809993003278755)
              ·
                refine ⟨4780431560714989504918133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186954373809993003278755 4780431560714989504918133)
                ·
                  refine ⟨448165458817030266086075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4780431560714989504918133 448165458817030266086075)
                  ·
                    rfl

theorem cell20_981899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_981899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_981899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_981899 prefixEnd_981899 := by exact prefixLift 981899
  have htrace : WordTrace (prefixWord ++ tailWord_981899) baseStart_981899 baseEnd_981899 := by
    simpa [prefixWord, tailWord_981899, baseEnd_981899] using wordTrace_append hprefix tailTrace_981899
  have hstable : (prefixWord ++ tailWord_981899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981899).length < 2 ^ (prefixWord ++ tailWord_981899).sum := by decide
  have hdescent : baseEnd_981899 < baseStart_981899 := by decide
  rcases family_descends (prefixWord ++ tailWord_981899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982005 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 3]
def baseStart_982005 : Nat := 118140960795 + 982005 * 2 ^ 59
def prefixEnd_982005 : Nat := 4983230072969 + 3 ^ 40 * 982005 * 2
def baseEnd_982005 : Nat := 448213840105365008552309

theorem tailTrace_982005 : CollatzResearch.WordTrace tailWord_982005 prefixEnd_982005 448213840105365008552309 := by
  unfold tailWord_982005
  simp only [CollatzResearch.WordTrace]
  refine ⟨35816664807371072946787469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23877776538247381964524979 35816664807371072946787469)
  ·
    refine ⟨13431249302764152355045301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35816664807371072946787469 13431249302764152355045301)
    ·
      refine ⟨1259179622134139283285497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13431249302764152355045301 1259179622134139283285497)
      ·
        refine ⟨944384716600604462464123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1259179622134139283285497 944384716600604462464123)
        ·
          refine ⟨1416577074900906693696185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944384716600604462464123 1416577074900906693696185)
          ·
            refine ⟨1062432806175680020272139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1416577074900906693696185 1062432806175680020272139)
            ·
              refine ⟨1593649209263520030408209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062432806175680020272139 1593649209263520030408209)
              ·
                refine ⟨1195236906947640022806157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593649209263520030408209 1195236906947640022806157)
                ·
                  refine ⟨448213840105365008552309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195236906947640022806157 448213840105365008552309)
                  ·
                    rfl

theorem cell20_982005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_982005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982005 prefixEnd_982005 := by exact prefixLift 982005
  have htrace : WordTrace (prefixWord ++ tailWord_982005) baseStart_982005 baseEnd_982005 := by
    simpa [prefixWord, tailWord_982005, baseEnd_982005] using wordTrace_append hprefix tailTrace_982005
  have hstable : (prefixWord ++ tailWord_982005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982005).length < 2 ^ (prefixWord ++ tailWord_982005).sum := by decide
  have hdescent : baseEnd_982005 < baseStart_982005 := by decide
  rcases family_descends (prefixWord ++ tailWord_982005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982037 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_982037 : Nat := 118140960795 + 982037 * 2 ^ 59
def prefixEnd_982037 : Nat := 4983230072969 + 3 ^ 40 * 982037 * 2
def baseEnd_982037 : Nat := 448228445777315119485511

theorem tailTrace_982037 : CollatzResearch.WordTrace tailWord_982037 prefixEnd_982037 448228445777315119485511 := by
  unfold tailWord_982037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35817831943255142411952365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23878554628836761607968243 35817831943255142411952365)
  ·
    refine ⟨13431686978720678404482137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35817831943255142411952365 13431686978720678404482137)
    ·
      refine ⟨10073765234040508803361603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13431686978720678404482137 10073765234040508803361603)
      ·
        refine ⟨15110647851060763205042405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073765234040508803361603 15110647851060763205042405)
        ·
          refine ⟨2833246472073893100945451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15110647851060763205042405 2833246472073893100945451)
          ·
            refine ⟨4249869708110839651418177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833246472073893100945451 4249869708110839651418177)
            ·
              refine ⟨3187402281083129738563633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4249869708110839651418177 3187402281083129738563633)
              ·
                refine ⟨2390551710812347303922725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3187402281083129738563633 2390551710812347303922725)
                ·
                  refine ⟨448228445777315119485511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2390551710812347303922725 448228445777315119485511)
                  ·
                    rfl

theorem cell20_982037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_982037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982037 prefixEnd_982037 := by exact prefixLift 982037
  have htrace : WordTrace (prefixWord ++ tailWord_982037) baseStart_982037 baseEnd_982037 := by
    simpa [prefixWord, tailWord_982037, baseEnd_982037] using wordTrace_append hprefix tailTrace_982037
  have hstable : (prefixWord ++ tailWord_982037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982037).length < 2 ^ (prefixWord ++ tailWord_982037).sum := by decide
  have hdescent : baseEnd_982037 < baseStart_982037 := by decide
  rcases family_descends (prefixWord ++ tailWord_982037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982051 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_982051 : Nat := 118140960795 + 982051 * 2 ^ 59
def prefixEnd_982051 : Nat := 4983230072969 + 3 ^ 40 * 982051 * 2
def baseEnd_982051 : Nat := 448234835758793293018787

theorem tailTrace_982051 : CollatzResearch.WordTrace tailWord_982051 prefixEnd_982051 448234835758793293018787 := by
  unfold tailWord_982051
  simp only [CollatzResearch.WordTrace]
  refine ⟨35818342565204422802962007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23878895043469615201974671 35818342565204422802962007)
  ·
    refine ⟨53727513847806634204443011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35818342565204422802962007 53727513847806634204443011)
    ·
      refine ⟨80591270771709951306664517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53727513847806634204443011 80591270771709951306664517)
      ·
        refine ⟨15110863269695615869999597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80591270771709951306664517 15110863269695615869999597)
        ·
          refine ⟨5666573726135855951249849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15110863269695615869999597 5666573726135855951249849)
          ·
            refine ⟨4249930294601891963437387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5666573726135855951249849 4249930294601891963437387)
            ·
              refine ⟨6374895441902837945156081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249930294601891963437387 6374895441902837945156081)
              ·
                refine ⟨4781171581427128458867061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6374895441902837945156081 4781171581427128458867061)
                ·
                  refine ⟨448234835758793293018787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4781171581427128458867061 448234835758793293018787)
                  ·
                    rfl

theorem cell20_982051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_982051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982051 prefixEnd_982051 := by exact prefixLift 982051
  have htrace : WordTrace (prefixWord ++ tailWord_982051) baseStart_982051 baseEnd_982051 := by
    simpa [prefixWord, tailWord_982051, baseEnd_982051] using wordTrace_append hprefix tailTrace_982051
  have hstable : (prefixWord ++ tailWord_982051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982051).length < 2 ^ (prefixWord ++ tailWord_982051).sum := by decide
  have hdescent : baseEnd_982051 < baseStart_982051 := by decide
  rcases family_descends (prefixWord ++ tailWord_982051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982081 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 3]
def baseStart_982081 : Nat := 118140960795 + 982081 * 2 ^ 59
def prefixEnd_982081 : Nat := 4983230072969 + 3 ^ 40 * 982081 * 2
def baseEnd_982081 : Nat := 448248528576246522018665

theorem tailTrace_982081 : CollatzResearch.WordTrace tailWord_982081 prefixEnd_982081 448248528576246522018665 := by
  unfold tailWord_982081
  simp only [CollatzResearch.WordTrace]
  refine ⟨35819436755095737926554097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23879624503397158617702731 35819436755095737926554097)
  ·
    refine ⟨26864577566321803444915573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35819436755095737926554097 26864577566321803444915573)
    ·
      refine ⟨2518554146842669072960835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26864577566321803444915573 2518554146842669072960835)
      ·
        refine ⟨3777831220264003609441253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2518554146842669072960835 3777831220264003609441253)
        ·
          refine ⟨708343353799500676770235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3777831220264003609441253 708343353799500676770235)
          ·
            refine ⟨1062515030699251015155353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708343353799500676770235 1062515030699251015155353)
            ·
              refine ⟨796886273024438261366515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062515030699251015155353 796886273024438261366515)
              ·
                refine ⟨1195329409536657392049773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796886273024438261366515 1195329409536657392049773)
                ·
                  refine ⟨448248528576246522018665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195329409536657392049773 448248528576246522018665)
                  ·
                    rfl

theorem cell20_982081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_982081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982081 prefixEnd_982081 := by exact prefixLift 982081
  have htrace : WordTrace (prefixWord ++ tailWord_982081) baseStart_982081 baseEnd_982081 := by
    simpa [prefixWord, tailWord_982081, baseEnd_982081] using wordTrace_append hprefix tailTrace_982081
  have hstable : (prefixWord ++ tailWord_982081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982081).length < 2 ^ (prefixWord ++ tailWord_982081).sum := by decide
  have hdescent : baseEnd_982081 < baseStart_982081 := by decide
  rcases family_descends (prefixWord ++ tailWord_982081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982096 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_982096 : Nat := 118140960795 + 982096 * 2 ^ 59
def prefixEnd_982096 : Nat := 4983230072969 + 3 ^ 40 * 982096 * 2
def baseEnd_982096 : Nat := 448255374984973136518603

theorem tailTrace_982096 : CollatzResearch.WordTrace tailWord_982096 prefixEnd_982096 448255374984973136518603 := by
  unfold tailWord_982096
  simp only [CollatzResearch.WordTrace]
  refine ⟨17909991925020697744175071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23879989233360930325566761 17909991925020697744175071)
  ·
    refine ⟨26864987887531046616262607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17909991925020697744175071 26864987887531046616262607)
    ·
      refine ⟨40297481831296569924393911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26864987887531046616262607 40297481831296569924393911)
      ·
        refine ⟨60446222746944854886590867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40297481831296569924393911 60446222746944854886590867)
        ·
          refine ⟨90669334120417282329886301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60446222746944854886590867 90669334120417282329886301)
          ·
            refine ⟨34001000295156480873707363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90669334120417282329886301 34001000295156480873707363)
            ·
              refine ⟨51001500442734721310561045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34001000295156480873707363 51001500442734721310561045)
              ·
                refine ⟨2390695333253190061432549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51001500442734721310561045 2390695333253190061432549)
                ·
                  refine ⟨448255374984973136518603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2390695333253190061432549 448255374984973136518603)
                  ·
                    rfl

theorem cell20_982096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_982096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982096 prefixEnd_982096 := by exact prefixLift 982096
  have htrace : WordTrace (prefixWord ++ tailWord_982096) baseStart_982096 baseEnd_982096 := by
    simpa [prefixWord, tailWord_982096, baseEnd_982096] using wordTrace_append hprefix tailTrace_982096
  have hstable : (prefixWord ++ tailWord_982096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982096).length < 2 ^ (prefixWord ++ tailWord_982096).sum := by decide
  have hdescent : baseEnd_982096 < baseStart_982096 := by decide
  rcases family_descends (prefixWord ++ tailWord_982096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982120 : List Nat := [2, 1, 4, 4, 9]
def baseStart_982120 : Nat := 118140960795 + 982120 * 2 ^ 59
def prefixEnd_982120 : Nat := 4983230072969 + 3 ^ 40 * 982120 * 2
def baseEnd_982120 : Nat := 5534152212826366910105

theorem tailTrace_982120 : CollatzResearch.WordTrace tailWord_982120 prefixEnd_982120 5534152212826366910105 := by
  unfold tailWord_982120
  simp only [CollatzResearch.WordTrace]
  refine ⟨17910429600977223793611907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23880572801302965058149209 17910429600977223793611907)
  ·
    refine ⟨26865644401465835690417861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17910429600977223793611907 26865644401465835690417861)
    ·
      refine ⟨5037308325274844191953349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26865644401465835690417861 5037308325274844191953349)
      ·
        refine ⟨944495310989033285991253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5037308325274844191953349 944495310989033285991253)
        ·
          refine ⟨5534152212826366910105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 944495310989033285991253 5534152212826366910105)
          ·
            rfl

theorem cell20_982120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 9].length) (baseStart_982120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982120 prefixEnd_982120 := by exact prefixLift 982120
  have htrace : WordTrace (prefixWord ++ tailWord_982120) baseStart_982120 baseEnd_982120 := by
    simpa [prefixWord, tailWord_982120, baseEnd_982120] using wordTrace_append hprefix tailTrace_982120
  have hstable : (prefixWord ++ tailWord_982120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982120).length < 2 ^ (prefixWord ++ tailWord_982120).sum := by decide
  have hdescent : baseEnd_982120 < baseStart_982120 := by decide
  rcases family_descends (prefixWord ++ tailWord_982120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982126 : List Nat := [4, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_982126 : Nat := 118140960795 + 982126 * 2 ^ 59
def prefixEnd_982126 : Nat := 4983230072969 + 3 ^ 40 * 982126 * 2
def baseEnd_982126 : Nat := 448269067802426365518481

theorem tailTrace_982126 : CollatzResearch.WordTrace tailWord_982126 prefixEnd_982126 448269067802426365518481 := by
  unfold tailWord_982126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4477634754991588826492779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23880718693288473741294821 4477634754991588826492779)
  ·
    refine ⟨6716452132487383239739169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4477634754991588826492779 6716452132487383239739169)
    ·
      refine ⟨5037339099365537429804377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6716452132487383239739169 5037339099365537429804377)
      ·
        refine ⟨3778004324524153072353283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5037339099365537429804377 3778004324524153072353283)
        ·
          refine ⟨5667006486786229608529925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778004324524153072353283 5667006486786229608529925)
          ·
            refine ⟨1062563716272418051599361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5667006486786229608529925 1062563716272418051599361)
            ·
              refine ⟨796922787204313538699521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062563716272418051599361 796922787204313538699521)
              ·
                refine ⟨597692090403235154024641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796922787204313538699521 597692090403235154024641)
                ·
                  refine ⟨448269067802426365518481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597692090403235154024641 448269067802426365518481)
                  ·
                    rfl

theorem cell20_982126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_982126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982126 prefixEnd_982126 := by exact prefixLift 982126
  have htrace : WordTrace (prefixWord ++ tailWord_982126) baseStart_982126 baseEnd_982126 := by
    simpa [prefixWord, tailWord_982126, baseEnd_982126] using wordTrace_append hprefix tailTrace_982126
  have hstable : (prefixWord ++ tailWord_982126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982126).length < 2 ^ (prefixWord ++ tailWord_982126).sum := by decide
  have hdescent : baseEnd_982126 < baseStart_982126 := by decide
  rcases family_descends (prefixWord ++ tailWord_982126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982130 : List Nat := [3, 2, 1, 2, 2, 1, 3, 4, 2]
def baseStart_982130 : Nat := 118140960795 + 982130 * 2 ^ 59
def prefixEnd_982130 : Nat := 4983230072969 + 3 ^ 40 * 982130 * 2
def baseEnd_982130 : Nat := 448270893511420129385131

theorem tailTrace_982130 : CollatzResearch.WordTrace tailWord_982130 prefixEnd_982130 448270893511420129385131 := by
  unfold tailWord_982130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8955305982979554823771961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23880815954612146196725229 8955305982979554823771961)
  ·
    refine ⟨6716479487234666117828971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8955305982979554823771961 6716479487234666117828971)
    ·
      refine ⟨10074719230851999176743457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6716479487234666117828971 10074719230851999176743457)
      ·
        refine ⟨7556039423138999382557593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10074719230851999176743457 7556039423138999382557593)
        ·
          refine ⟨5667029567354249536918195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7556039423138999382557593 5667029567354249536918195)
          ·
            refine ⟨8500544351031374305377293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5667029567354249536918195 8500544351031374305377293)
            ·
              refine ⟨3187704131636765364516485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8500544351031374305377293 3187704131636765364516485)
              ·
                refine ⟨597694524681893505846841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3187704131636765364516485 597694524681893505846841)
                ·
                  refine ⟨448270893511420129385131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597694524681893505846841 448270893511420129385131)
                  ·
                    rfl

theorem cell20_982130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_982130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982130 prefixEnd_982130 := by exact prefixLift 982130
  have htrace : WordTrace (prefixWord ++ tailWord_982130) baseStart_982130 baseEnd_982130 := by
    simpa [prefixWord, tailWord_982130, baseEnd_982130] using wordTrace_append hprefix tailTrace_982130
  have hstable : (prefixWord ++ tailWord_982130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982130).length < 2 ^ (prefixWord ++ tailWord_982130).sum := by decide
  have hdescent : baseEnd_982130 < baseStart_982130 := by decide
  rcases family_descends (prefixWord ++ tailWord_982130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982133 : List Nat := [1, 3, 4, 3, 2, 1, 1, 5]
def baseStart_982133 : Nat := 118140960795 + 982133 * 2 ^ 59
def prefixEnd_982133 : Nat := 4983230072969 + 3 ^ 40 * 982133 * 2
def baseEnd_982133 : Nat := 149424087597721817428373

theorem tailTrace_982133 : CollatzResearch.WordTrace tailWord_982133 prefixEnd_982133 149424087597721817428373 := by
  unfold tailWord_982133
  simp only [CollatzResearch.WordTrace]
  refine ⟨35821333350907350807447053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23880888900604900538298035 35821333350907350807447053)
  ·
    refine ⟨13433000006590256552792645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35821333350907350807447053 13433000006590256552792645)
    ·
      refine ⟨2518687501235673103648621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13433000006590256552792645 2518687501235673103648621)
      ·
        refine ⟨944507812963377413868233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2518687501235673103648621 944507812963377413868233)
        ·
          refine ⟨708380859722533060401175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944507812963377413868233 708380859722533060401175)
          ·
            refine ⟨1062571289583799590601763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708380859722533060401175 1062571289583799590601763)
            ·
              refine ⟨1593856934375699385902645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062571289583799590601763 1593856934375699385902645)
              ·
                refine ⟨149424087597721817428373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1593856934375699385902645 149424087597721817428373)
                ·
                  rfl

theorem cell20_982133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 5].length) (baseStart_982133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982133 prefixEnd_982133 := by exact prefixLift 982133
  have htrace : WordTrace (prefixWord ++ tailWord_982133) baseStart_982133 baseEnd_982133 := by
    simpa [prefixWord, tailWord_982133, baseEnd_982133] using wordTrace_append hprefix tailTrace_982133
  have hstable : (prefixWord ++ tailWord_982133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982133).length < 2 ^ (prefixWord ++ tailWord_982133).sum := by decide
  have hdescent : baseEnd_982133 < baseStart_982133 := by decide
  rcases family_descends (prefixWord ++ tailWord_982133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982137 : List Nat := [1, 2, 1, 3, 5, 2, 1, 5]
def baseStart_982137 : Nat := 118140960795 + 982137 * 2 ^ 59
def prefixEnd_982137 : Nat := 4983230072969 + 3 ^ 40 * 982137 * 2
def baseEnd_982137 : Nat := 149424696167386405383923

theorem tailTrace_982137 : CollatzResearch.WordTrace tailWord_982137 prefixEnd_982137 149424696167386405383923 := by
  unfold tailWord_982137
  simp only [CollatzResearch.WordTrace]
  refine ⟨35821479242892859490592665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23880986161928572993728443 35821479242892859490592665)
  ·
    refine ⟨26866109432169644617944499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35821479242892859490592665 26866109432169644617944499)
    ·
      refine ⟨40299164148254466926916749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26866109432169644617944499 40299164148254466926916749)
      ·
        refine ⟨15112186555595425097593781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40299164148254466926916749 15112186555595425097593781)
        ·
          refine ⟨1416767489587071102899417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15112186555595425097593781 1416767489587071102899417)
          ·
            refine ⟨1062575617190303327174563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1416767489587071102899417 1062575617190303327174563)
            ·
              refine ⟨1593863425785454990761845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062575617190303327174563 1593863425785454990761845)
              ·
                refine ⟨149424696167386405383923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1593863425785454990761845 149424696167386405383923)
                ·
                  rfl

theorem cell20_982137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 5].length) (baseStart_982137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982137 prefixEnd_982137 := by exact prefixLift 982137
  have htrace : WordTrace (prefixWord ++ tailWord_982137) baseStart_982137 baseEnd_982137 := by
    simpa [prefixWord, tailWord_982137, baseEnd_982137] using wordTrace_append hprefix tailTrace_982137
  have hstable : (prefixWord ++ tailWord_982137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982137).length < 2 ^ (prefixWord ++ tailWord_982137).sum := by decide
  have hdescent : baseEnd_982137 < baseStart_982137 := by decide
  rcases family_descends (prefixWord ++ tailWord_982137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982168 : List Nat := [2, 1, 2, 4, 2, 1, 1, 5, 2]
def baseStart_982168 : Nat := 118140960795 + 982168 * 2 ^ 59
def prefixEnd_982168 : Nat := 4983230072969 + 3 ^ 40 * 982168 * 2
def baseEnd_982168 : Nat := 448288237746860886118309

theorem tailTrace_982168 : CollatzResearch.WordTrace tailWord_982168 prefixEnd_982168 448288237746860886118309 := by
  unfold tailWord_982168
  simp only [CollatzResearch.WordTrace]
  refine ⟨17911304952890275892485579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23881739937187034523314105 17911304952890275892485579)
  ·
    refine ⟨26866957429335413838728369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17911304952890275892485579 26866957429335413838728369)
    ·
      refine ⟨20150218072001560379046277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26866957429335413838728369 20150218072001560379046277)
      ·
        refine ⟨3778165888500292571071177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20150218072001560379046277 3778165888500292571071177)
        ·
          refine ⟨2833624416375219428303383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3778165888500292571071177 2833624416375219428303383)
          ·
            refine ⟨4250436624562829142455075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833624416375219428303383 4250436624562829142455075)
            ·
              refine ⟨6375654936844243713682613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250436624562829142455075 6375654936844243713682613)
              ·
                refine ⟨597717650329147848157745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6375654936844243713682613 597717650329147848157745)
                ·
                  refine ⟨448288237746860886118309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597717650329147848157745 448288237746860886118309)
                  ·
                    rfl

theorem cell20_982168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_982168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982168 prefixEnd_982168 := by exact prefixLift 982168
  have htrace : WordTrace (prefixWord ++ tailWord_982168) baseStart_982168 baseEnd_982168 := by
    simpa [prefixWord, tailWord_982168, baseEnd_982168] using wordTrace_append hprefix tailTrace_982168
  have hstable : (prefixWord ++ tailWord_982168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982168).length < 2 ^ (prefixWord ++ tailWord_982168).sum := by decide
  have hdescent : baseEnd_982168 < baseStart_982168 := by decide
  rcases family_descends (prefixWord ++ tailWord_982168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982178 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_982178 : Nat := 118140960795 + 982178 * 2 ^ 59
def prefixEnd_982178 : Nat := 4983230072969 + 3 ^ 40 * 982178 * 2
def baseEnd_982178 : Nat := 448292802019345295784935

theorem tailTrace_982178 : CollatzResearch.WordTrace tailWord_982178 prefixEnd_982178 448292802019345295784935 := by
  unfold tailWord_982178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8955743658936080873208797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23881983090496215661890125 8955743658936080873208797)
  ·
    refine ⟨3358403872101030327453299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8955743658936080873208797 3358403872101030327453299)
    ·
      refine ⟨5037605808151545491179949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358403872101030327453299 5037605808151545491179949)
      ·
        refine ⟨1889102178056829559192481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5037605808151545491179949 1889102178056829559192481)
        ·
          refine ⟨1416826633542622169394361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1889102178056829559192481 1416826633542622169394361)
          ·
            refine ⟨1062619975156966627045771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1416826633542622169394361 1062619975156966627045771)
            ·
              refine ⟨1593929962735449940568657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062619975156966627045771 1593929962735449940568657)
              ·
                refine ⟨1195447472051587455426493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593929962735449940568657 1195447472051587455426493)
                ·
                  refine ⟨448292802019345295784935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195447472051587455426493 448292802019345295784935)
                  ·
                    rfl

theorem cell20_982178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_982178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982178 prefixEnd_982178 := by exact prefixLift 982178
  have htrace : WordTrace (prefixWord ++ tailWord_982178) baseStart_982178 baseEnd_982178 := by
    simpa [prefixWord, tailWord_982178, baseEnd_982178] using wordTrace_append hprefix tailTrace_982178
  have hstable : (prefixWord ++ tailWord_982178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982178).length < 2 ^ (prefixWord ++ tailWord_982178).sum := by decide
  have hdescent : baseEnd_982178 < baseStart_982178 := by decide
  rcases family_descends (prefixWord ++ tailWord_982178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982230 : List Nat := [5, 2, 1, 2, 2, 2, 6]
def baseStart_982230 : Nat := 118140960795 + 982230 * 2 ^ 59
def prefixEnd_982230 : Nat := 4983230072969 + 3 ^ 40 * 982230 * 2
def baseEnd_982230 : Nat := 49812948470696025116821

theorem tailTrace_982230 : CollatzResearch.WordTrace tailWord_982230 prefixEnd_982230 49812948470696025116821 := by
  unfold tailWord_982230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239054451972246023358009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23883247487703957582485429 2239054451972246023358009)
  ·
    refine ⟨1679290838979184517518507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2239054451972246023358009 1679290838979184517518507)
    ·
      refine ⟨2518936258468776776277761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1679290838979184517518507 2518936258468776776277761)
      ·
        refine ⟨1889202193851582582208321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2518936258468776776277761 1889202193851582582208321)
        ·
          refine ⟨1416901645388686936656241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1889202193851582582208321 1416901645388686936656241)
          ·
            refine ⟨1062676234041515202492181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1416901645388686936656241 1062676234041515202492181)
            ·
              refine ⟨49812948470696025116821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1062676234041515202492181 49812948470696025116821)
              ·
                rfl

theorem cell20_982230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 6].length) (baseStart_982230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982230 prefixEnd_982230 := by exact prefixLift 982230
  have htrace : WordTrace (prefixWord ++ tailWord_982230) baseStart_982230 baseEnd_982230 := by
    simpa [prefixWord, tailWord_982230, baseEnd_982230] using wordTrace_append hprefix tailTrace_982230
  have hstable : (prefixWord ++ tailWord_982230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982230).length < 2 ^ (prefixWord ++ tailWord_982230).sum := by decide
  have hdescent : baseEnd_982230 < baseStart_982230 := by decide
  rcases family_descends (prefixWord ++ tailWord_982230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982241 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_982241 : Nat := 118140960795 + 982241 * 2 ^ 59
def prefixEnd_982241 : Nat := 4983230072969 + 3 ^ 40 * 982241 * 2
def baseEnd_982241 : Nat := 448321556935997076684677

theorem tailTrace_982241 : CollatzResearch.WordTrace tailWord_982241 prefixEnd_982241 448321556935997076684677 := by
  unfold tailWord_982241
  simp only [CollatzResearch.WordTrace]
  refine ⟨35825272434516085252378577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23883514956344056834919051 35825272434516085252378577)
  ·
    refine ⟨26868954325887063939283933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35825272434516085252378577 26868954325887063939283933)
    ·
      refine ⟨10075857872207648977231475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26868954325887063939283933 10075857872207648977231475)
      ·
        refine ⟨15113786808311473465847213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10075857872207648977231475 15113786808311473465847213)
        ·
          refine ⟨5667670053116802549692705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15113786808311473465847213 5667670053116802549692705)
          ·
            refine ⟨4250752539837601912269529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5667670053116802549692705 4250752539837601912269529)
            ·
              refine ⟨3188064404878201434202147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4250752539837601912269529 3188064404878201434202147)
              ·
                refine ⟨4782096607317302151303221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188064404878201434202147 4782096607317302151303221)
                ·
                  refine ⟨448321556935997076684677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4782096607317302151303221 448321556935997076684677)
                  ·
                    rfl

theorem cell20_982241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_982241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982241 prefixEnd_982241 := by exact prefixLift 982241
  have htrace : WordTrace (prefixWord ++ tailWord_982241) baseStart_982241 baseEnd_982241 := by
    simpa [prefixWord, tailWord_982241, baseEnd_982241] using wordTrace_append hprefix tailTrace_982241
  have hstable : (prefixWord ++ tailWord_982241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982241).length < 2 ^ (prefixWord ++ tailWord_982241).sum := by decide
  have hdescent : baseEnd_982241 < baseStart_982241 := by decide
  rcases family_descends (prefixWord ++ tailWord_982241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982296 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 3]
def baseStart_982296 : Nat := 118140960795 + 982296 * 2 ^ 59
def prefixEnd_982296 : Nat := 4983230072969 + 3 ^ 40 * 982296 * 2
def baseEnd_982296 : Nat := 448346660434661329851119

theorem tailTrace_982296 : CollatzResearch.WordTrace tailWord_982296 prefixEnd_982296 448346660434661329851119 := by
  unfold tailWord_982296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17913639224658414822815371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23884852299544553097087161 17913639224658414822815371)
  ·
    refine ⟨26870458836987622234223057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17913639224658414822815371 26870458836987622234223057)
    ·
      refine ⟨20152844127740716675667293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26870458836987622234223057 20152844127740716675667293)
      ·
        refine ⟨7557316547902768753375235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20152844127740716675667293 7557316547902768753375235)
        ·
          refine ⟨11335974821854153130062853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557316547902768753375235 11335974821854153130062853)
          ·
            refine ⟨2125495279097653711886785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11335974821854153130062853 2125495279097653711886785)
            ·
              refine ⟨1594121459323240283915089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2125495279097653711886785 1594121459323240283915089)
              ·
                refine ⟨1195591094492430212936317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1594121459323240283915089 1195591094492430212936317)
                ·
                  refine ⟨448346660434661329851119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195591094492430212936317 448346660434661329851119)
                  ·
                    rfl

theorem cell20_982296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_982296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982296 prefixEnd_982296 := by exact prefixLift 982296
  have htrace : WordTrace (prefixWord ++ tailWord_982296) baseStart_982296 baseEnd_982296 := by
    simpa [prefixWord, tailWord_982296, baseEnd_982296] using wordTrace_append hprefix tailTrace_982296
  have hstable : (prefixWord ++ tailWord_982296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982296).length < 2 ^ (prefixWord ++ tailWord_982296).sum := by decide
  have hdescent : baseEnd_982296 < baseStart_982296 := by decide
  rcases family_descends (prefixWord ++ tailWord_982296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982306 : List Nat := [3, 3, 1, 1, 5, 1, 1, 5]
def baseStart_982306 : Nat := 118140960795 + 982306 * 2 ^ 59
def prefixEnd_982306 : Nat := 4983230072969 + 3 ^ 40 * 982306 * 2
def baseEnd_982306 : Nat := 149450408235715246505915

theorem tailTrace_982306 : CollatzResearch.WordTrace tailWord_982306 prefixEnd_982306 149450408235715246505915 := by
  unfold tailWord_982306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8956910794820150338373693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23885095452853734235663181 8956910794820150338373693)
  ·
    refine ⟨3358841548057556376890135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8956910794820150338373693 3358841548057556376890135)
    ·
      refine ⟨5038262322086334565335203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358841548057556376890135 5038262322086334565335203)
      ·
        refine ⟨7557393483129501848002805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5038262322086334565335203 7557393483129501848002805)
        ·
          refine ⟨708505639043390798250263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7557393483129501848002805 708505639043390798250263)
          ·
            refine ⟨1062758458565086197375395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708505639043390798250263 1062758458565086197375395)
            ·
              refine ⟨1594137687847629296063093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062758458565086197375395 1594137687847629296063093)
              ·
                refine ⟨149450408235715246505915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1594137687847629296063093 149450408235715246505915)
                ·
                  rfl

theorem cell20_982306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_982306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982306 prefixEnd_982306 := by exact prefixLift 982306
  have htrace : WordTrace (prefixWord ++ tailWord_982306) baseStart_982306 baseEnd_982306 := by
    simpa [prefixWord, tailWord_982306, baseEnd_982306] using wordTrace_append hprefix tailTrace_982306
  have hstable : (prefixWord ++ tailWord_982306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982306).length < 2 ^ (prefixWord ++ tailWord_982306).sum := by decide
  have hdescent : baseEnd_982306 < baseStart_982306 := by decide
  rcases family_descends (prefixWord ++ tailWord_982306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982337 : List Nat := [1, 2, 5, 2, 1, 2, 2, 3, 2]
def baseStart_982337 : Nat := 118140960795 + 982337 * 2 ^ 59
def prefixEnd_982337 : Nat := 4983230072969 + 3 ^ 40 * 982337 * 2
def baseEnd_982337 : Nat := 448365373951847409484285

theorem tailTrace_982337 : CollatzResearch.WordTrace tailWord_982337 prefixEnd_982337 448365373951847409484285 := by
  unfold tailWord_982337
  simp only [CollatzResearch.WordTrace]
  refine ⟨35828773842168293647873265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23885849228112195765248843 35828773842168293647873265)
  ·
    refine ⟨26871580381626220235904949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35828773842168293647873265 26871580381626220235904949)
    ·
      refine ⟨2519210660777458147116089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26871580381626220235904949 2519210660777458147116089)
      ·
        refine ⟨1889407995583093610337067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2519210660777458147116089 1889407995583093610337067)
        ·
          refine ⟨2834111993374640415505601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889407995583093610337067 2834111993374640415505601)
          ·
            refine ⟨2125583995030980311629201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2834111993374640415505601 2125583995030980311629201)
            ·
              refine ⟨1594187996273235233721901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2125583995030980311629201 1594187996273235233721901)
              ·
                refine ⟨597820498602463212645713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1594187996273235233721901 597820498602463212645713)
                ·
                  refine ⟨448365373951847409484285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597820498602463212645713 448365373951847409484285)
                  ·
                    rfl

theorem cell20_982337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_982337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982337 prefixEnd_982337 := by exact prefixLift 982337
  have htrace : WordTrace (prefixWord ++ tailWord_982337) baseStart_982337 baseEnd_982337 := by
    simpa [prefixWord, tailWord_982337, baseEnd_982337] using wordTrace_append hprefix tailTrace_982337
  have hstable : (prefixWord ++ tailWord_982337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982337).length < 2 ^ (prefixWord ++ tailWord_982337).sum := by decide
  have hdescent : baseEnd_982337 < baseStart_982337 := by decide
  rcases family_descends (prefixWord ++ tailWord_982337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982362 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_982362 : Nat := 118140960795 + 982362 * 2 ^ 59
def prefixEnd_982362 : Nat := 4983230072969 + 3 ^ 40 * 982362 * 2
def baseEnd_982362 : Nat := 448376784633058433650849

theorem tailTrace_982362 : CollatzResearch.WordTrace tailWord_982362 prefixEnd_982362 448376784633058433650849 := by
  unfold tailWord_982362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8957421416769430729383335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23886457111385148611688893 8957421416769430729383335)
  ·
    refine ⟨13436132125154146094075003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8957421416769430729383335 13436132125154146094075003)
    ·
      refine ⟨20154198187731219141112505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13436132125154146094075003 20154198187731219141112505)
      ·
        refine ⟨15115648640798414355834379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20154198187731219141112505 15115648640798414355834379)
        ·
          refine ⟨22673472961197621533751569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15115648640798414355834379 22673472961197621533751569)
          ·
            refine ⟨17005104720898216150313677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22673472961197621533751569 17005104720898216150313677)
            ·
              refine ⟨6376914270336831056367629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17005104720898216150313677 6376914270336831056367629)
              ·
                refine ⟨2391342851376311646137861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6376914270336831056367629 2391342851376311646137861)
                ·
                  refine ⟨448376784633058433650849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2391342851376311646137861 448376784633058433650849)
                  ·
                    rfl

theorem cell20_982362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_982362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982362 prefixEnd_982362 := by exact prefixLift 982362
  have htrace : WordTrace (prefixWord ++ tailWord_982362) baseStart_982362 baseEnd_982362 := by
    simpa [prefixWord, tailWord_982362, baseEnd_982362] using wordTrace_append hprefix tailTrace_982362
  have hstable : (prefixWord ++ tailWord_982362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982362).length < 2 ^ (prefixWord ++ tailWord_982362).sum := by decide
  have hdescent : baseEnd_982362 < baseStart_982362 := by decide
  rcases family_descends (prefixWord ++ tailWord_982362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982407 : List Nat := [1, 1, 4, 2, 2, 2, 8]
def baseStart_982407 : Nat := 118140960795 + 982407 * 2 ^ 59
def prefixEnd_982407 : Nat := 4983230072969 + 3 ^ 40 * 982407 * 2
def baseEnd_982407 : Nat := 49821924873248697461185

theorem tailTrace_982407 : CollatzResearch.WordTrace tailWord_982407 prefixEnd_982407 49821924873248697461185 := by
  unfold tailWord_982407
  simp only [CollatzResearch.WordTrace]
  refine ⟨35831326951914695602921475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23887551301276463735280983 35831326951914695602921475)
  ·
    refine ⟨53746990427872043404382213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35831326951914695602921475 53746990427872043404382213)
    ·
      refine ⟨10077560705226008138321665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53746990427872043404382213 10077560705226008138321665)
      ·
        refine ⟨7558170528919506103741249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10077560705226008138321665 7558170528919506103741249)
        ·
          refine ⟨5668627896689629577805937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7558170528919506103741249 5668627896689629577805937)
          ·
            refine ⟨4251470922517222183354453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5668627896689629577805937 4251470922517222183354453)
            ·
              refine ⟨49821924873248697461185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4251470922517222183354453 49821924873248697461185)
              ·
                rfl

theorem cell20_982407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 8].length) (baseStart_982407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982407 prefixEnd_982407 := by exact prefixLift 982407
  have htrace : WordTrace (prefixWord ++ tailWord_982407) baseStart_982407 baseEnd_982407 := by
    simpa [prefixWord, tailWord_982407, baseEnd_982407] using wordTrace_append hprefix tailTrace_982407
  have hstable : (prefixWord ++ tailWord_982407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982407).length < 2 ^ (prefixWord ++ tailWord_982407).sum := by decide
  have hdescent : baseEnd_982407 < baseStart_982407 := by decide
  rcases family_descends (prefixWord ++ tailWord_982407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982455 : List Nat := [1, 1, 3, 1, 3, 2, 2, 5, 2]
def baseStart_982455 : Nat := 118140960795 + 982455 * 2 ^ 59
def prefixEnd_982455 : Nat := 4983230072969 + 3 ^ 40 * 982455 * 2
def baseEnd_982455 : Nat := 448419232367163443550469

theorem tailTrace_982455 : CollatzResearch.WordTrace tailWord_982455 prefixEnd_982455 448419232367163443550469 := by
  unfold tailWord_982455
  simp only [CollatzResearch.WordTrace]
  refine ⟨35833077655740799800668819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23888718437160533200445879 35833077655740799800668819)
  ·
    refine ⟨53749616483611199701003229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35833077655740799800668819 53749616483611199701003229)
    ·
      refine ⟨20156106181354199887876211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53749616483611199701003229 20156106181354199887876211)
      ·
        refine ⟨30234159272031299831814317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20156106181354199887876211 30234159272031299831814317)
        ·
          refine ⟨11337809727011737436930369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30234159272031299831814317 11337809727011737436930369)
          ·
            refine ⟨8503357295258803077697777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11337809727011737436930369 8503357295258803077697777)
            ·
              refine ⟨6377517971444102308273333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8503357295258803077697777 6377517971444102308273333)
              ·
                refine ⟨597892309822884591400625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6377517971444102308273333 597892309822884591400625)
                ·
                  refine ⟨448419232367163443550469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597892309822884591400625 448419232367163443550469)
                  ·
                    rfl

theorem cell20_982455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 2].length) (baseStart_982455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982455 prefixEnd_982455 := by exact prefixLift 982455
  have htrace : WordTrace (prefixWord ++ tailWord_982455) baseStart_982455 baseEnd_982455 := by
    simpa [prefixWord, tailWord_982455, baseEnd_982455] using wordTrace_append hprefix tailTrace_982455
  have hstable : (prefixWord ++ tailWord_982455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982455).length < 2 ^ (prefixWord ++ tailWord_982455).sum := by decide
  have hdescent : baseEnd_982455 < baseStart_982455 := by decide
  rcases family_descends (prefixWord ++ tailWord_982455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982468 : List Nat := [2, 3, 3, 2, 1, 3, 2, 2, 2]
def baseStart_982468 : Nat := 118140960795 + 982468 * 2 ^ 59
def prefixEnd_982468 : Nat := 4983230072969 + 3 ^ 40 * 982468 * 2
def baseEnd_982468 : Nat := 448425165921393176117083

theorem tailTrace_982468 : CollatzResearch.WordTrace tailWord_982468 prefixEnd_982468 448425165921393176117083 := by
  unfold tailWord_982468
  simp only [CollatzResearch.WordTrace]
  refine ⟨17916775902346851510446029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23889034536462468680594705 17916775902346851510446029)
  ·
    refine ⟨6718790963380069316417261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17916775902346851510446029 6718790963380069316417261)
    ·
      refine ⟨2519546611267525993656473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6718790963380069316417261 2519546611267525993656473)
      ·
        refine ⟨1889659958450644495242355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2519546611267525993656473 1889659958450644495242355)
        ·
          refine ⟨2834489937675966742863533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889659958450644495242355 2834489937675966742863533)
          ·
            refine ⟨1062933726628487528573825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2834489937675966742863533 1062933726628487528573825)
            ·
              refine ⟨797200294971365646430369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062933726628487528573825 797200294971365646430369)
              ·
                refine ⟨597900221228524234822777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797200294971365646430369 597900221228524234822777)
                ·
                  refine ⟨448425165921393176117083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597900221228524234822777 448425165921393176117083)
                  ·
                    rfl

theorem cell20_982468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_982468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982468 prefixEnd_982468 := by exact prefixLift 982468
  have htrace : WordTrace (prefixWord ++ tailWord_982468) baseStart_982468 baseEnd_982468 := by
    simpa [prefixWord, tailWord_982468, baseEnd_982468] using wordTrace_append hprefix tailTrace_982468
  have hstable : (prefixWord ++ tailWord_982468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982468).length < 2 ^ (prefixWord ++ tailWord_982468).sum := by decide
  have hdescent : baseEnd_982468 < baseStart_982468 := by decide
  rcases family_descends (prefixWord ++ tailWord_982468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982493 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 4]
def baseStart_982493 : Nat := 118140960795 + 982493 * 2 ^ 59
def prefixEnd_982493 : Nat := 4983230072969 + 3 ^ 40 * 982493 * 2
def baseEnd_982493 : Nat := 448436576602604200283647

theorem tailTrace_982493 : CollatzResearch.WordTrace tailWord_982493 prefixEnd_982493 448436576602604200283647 := by
  unfold tailWord_982493
  simp only [CollatzResearch.WordTrace]
  refine ⟨35834463629603132290552133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23889642419735421527034755 35834463629603132290552133)
  ·
    refine ⟨6718961930550587304478525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35834463629603132290552133 6718961930550587304478525)
    ·
      refine ⟨2519610723956470239179447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6718961930550587304478525 2519610723956470239179447)
      ·
        refine ⟨3779416085934705358769171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2519610723956470239179447 3779416085934705358769171)
        ·
          refine ⟨5669124128902058038153757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779416085934705358769171 5669124128902058038153757)
          ·
            refine ⟨2125921548338271764307659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5669124128902058038153757 2125921548338271764307659)
            ·
              refine ⟨3188882322507407646461489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125921548338271764307659 3188882322507407646461489)
              ·
                refine ⟨2391661741880555734846117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188882322507407646461489 2391661741880555734846117)
                ·
                  refine ⟨448436576602604200283647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2391661741880555734846117 448436576602604200283647)
                  ·
                    rfl

theorem cell20_982493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_982493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982493 prefixEnd_982493 := by exact prefixLift 982493
  have htrace : WordTrace (prefixWord ++ tailWord_982493) baseStart_982493 baseEnd_982493 := by
    simpa [prefixWord, tailWord_982493, baseEnd_982493] using wordTrace_append hprefix tailTrace_982493
  have hstable : (prefixWord ++ tailWord_982493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982493).length < 2 ^ (prefixWord ++ tailWord_982493).sum := by decide
  have hdescent : baseEnd_982493 < baseStart_982493 := by decide
  rcases family_descends (prefixWord ++ tailWord_982493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982510 : List Nat := [4, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_982510 : Nat := 118140960795 + 982510 * 2 ^ 59
def prefixEnd_982510 : Nat := 4983230072969 + 3 ^ 40 * 982510 * 2
def baseEnd_982510 : Nat := 448444335865827696716911

theorem tailTrace_982510 : CollatzResearch.WordTrace tailWord_982510 prefixEnd_982510 448444335865827696716911 := by
  unfold tailWord_982510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4479385458817693024240123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23890055780361029462613989 4479385458817693024240123)
  ·
    refine ⟨6719078188226539536360185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4479385458817693024240123 6719078188226539536360185)
    ·
      refine ⟨5039308641169904652270139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6719078188226539536360185 5039308641169904652270139)
      ·
        refine ⟨7558962961754856978405209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5039308641169904652270139 7558962961754856978405209)
        ·
          refine ⟨5669222221316142733803907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7558962961754856978405209 5669222221316142733803907)
          ·
            refine ⟨8503833331974214100705861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669222221316142733803907 8503833331974214100705861)
            ·
              refine ⟨1594468749745165143882349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8503833331974214100705861 1594468749745165143882349)
              ·
                refine ⟨597925781154436928955881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1594468749745165143882349 597925781154436928955881)
                ·
                  refine ⟨448444335865827696716911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597925781154436928955881 448444335865827696716911)
                  ·
                    rfl

theorem cell20_982510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_982510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982510 prefixEnd_982510 := by exact prefixLift 982510
  have htrace : WordTrace (prefixWord ++ tailWord_982510) baseStart_982510 baseEnd_982510 := by
    simpa [prefixWord, tailWord_982510, baseEnd_982510] using wordTrace_append hprefix tailTrace_982510
  have hstable : (prefixWord ++ tailWord_982510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982510).length < 2 ^ (prefixWord ++ tailWord_982510).sum := by decide
  have hdescent : baseEnd_982510 < baseStart_982510 := by decide
  rcases family_descends (prefixWord ++ tailWord_982510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982582 : List Nat := [5, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_982582 : Nat := 118140960795 + 982582 * 2 ^ 59
def prefixEnd_982582 : Nat := 4983230072969 + 3 ^ 40 * 982582 * 2
def baseEnd_982582 : Nat := 448477198627715446316617

theorem tailTrace_982582 : CollatzResearch.WordTrace tailWord_982582 prefixEnd_982582 448477198627715446316617 := by
  unfold tailWord_982582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239856857892543780658875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23891806484187133660361333 2239856857892543780658875)
  ·
    refine ⟨3359785286838815670988313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2239856857892543780658875 3359785286838815670988313)
    ·
      refine ⟨2519838965129111753241235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3359785286838815670988313 2519838965129111753241235)
      ·
        refine ⟨3779758447693667629861853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2519838965129111753241235 3779758447693667629861853)
        ·
          refine ⟨1417409417885125361198195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3779758447693667629861853 1417409417885125361198195)
          ·
            refine ⟨2126114126827688041797293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417409417885125361198195 2126114126827688041797293)
            ·
              refine ⟨797292797560383015673985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2126114126827688041797293 797292797560383015673985)
              ·
                refine ⟨597969598170287261755489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797292797560383015673985 597969598170287261755489)
                ·
                  refine ⟨448477198627715446316617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597969598170287261755489 448477198627715446316617)
                  ·
                    rfl

theorem cell20_982582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_982582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982582 prefixEnd_982582 := by exact prefixLift 982582
  have htrace : WordTrace (prefixWord ++ tailWord_982582) baseStart_982582 baseEnd_982582 := by
    simpa [prefixWord, tailWord_982582, baseEnd_982582] using wordTrace_append hprefix tailTrace_982582
  have hstable : (prefixWord ++ tailWord_982582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982582).length < 2 ^ (prefixWord ++ tailWord_982582).sum := by decide
  have hdescent : baseEnd_982582 < baseStart_982582 := by decide
  rcases family_descends (prefixWord ++ tailWord_982582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982586 : List Nat := [3, 1, 1, 1, 3, 2, 5, 2, 2]
def baseStart_982586 : Nat := 118140960795 + 982586 * 2 ^ 59
def prefixEnd_982586 : Nat := 4983230072969 + 3 ^ 40 * 982586 * 2
def baseEnd_982586 : Nat := 448479024336709210183267

theorem tailTrace_982586 : CollatzResearch.WordTrace tailWord_982586 prefixEnd_982586 448479024336709210183267 := by
  unfold tailWord_982586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959463904566552293421903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23891903745510806115791741 8959463904566552293421903)
  ·
    refine ⟨13439195856849828440132855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8959463904566552293421903 13439195856849828440132855)
    ·
      refine ⟨20158793785274742660199283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13439195856849828440132855 20158793785274742660199283)
      ·
        refine ⟨30238190677912113990298925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20158793785274742660199283 30238190677912113990298925)
        ·
          refine ⟨11339321504217042746362097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30238190677912113990298925 11339321504217042746362097)
          ·
            refine ⟨8504491128162782059771573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11339321504217042746362097 8504491128162782059771573)
            ·
              refine ⟨797296043265260818103585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8504491128162782059771573 797296043265260818103585)
              ·
                refine ⟨597972032448945613577689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797296043265260818103585 597972032448945613577689)
                ·
                  refine ⟨448479024336709210183267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597972032448945613577689 448479024336709210183267)
                  ·
                    rfl

theorem cell20_982586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_982586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982586 prefixEnd_982586 := by exact prefixLift 982586
  have htrace : WordTrace (prefixWord ++ tailWord_982586) baseStart_982586 baseEnd_982586 := by
    simpa [prefixWord, tailWord_982586, baseEnd_982586] using wordTrace_append hprefix tailTrace_982586
  have hstable : (prefixWord ++ tailWord_982586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982586).length < 2 ^ (prefixWord ++ tailWord_982586).sum := by decide
  have hdescent : baseEnd_982586 < baseStart_982586 := by decide
  rcases family_descends (prefixWord ++ tailWord_982586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982597 : List Nat := [1, 3, 1, 1, 1, 4, 4, 5]
def baseStart_982597 : Nat := 118140960795 + 982597 * 2 ^ 59
def prefixEnd_982597 : Nat := 4983230072969 + 3 ^ 40 * 982597 * 2
def baseEnd_982597 : Nat := 149494681678814020272185

theorem tailTrace_982597 : CollatzResearch.WordTrace tailWord_982597 prefixEnd_982597 149494681678814020272185 := by
  unfold tailWord_982597
  simp only [CollatzResearch.WordTrace]
  refine ⟨35838256821226358052338045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23892171214150905368225363 35838256821226358052338045)
  ·
    refine ⟨13439346307959884269626767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35838256821226358052338045 13439346307959884269626767)
    ·
      refine ⟨20159019461939826404440151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13439346307959884269626767 20159019461939826404440151)
      ·
        refine ⟨30238529192909739606660227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20159019461939826404440151 30238529192909739606660227)
        ·
          refine ⟨45357793789364609409990341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30238529192909739606660227 45357793789364609409990341)
          ·
            refine ⟨8504586335505864264373189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45357793789364609409990341 8504586335505864264373189)
            ·
              refine ⟨1594609937907349549569973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8504586335505864264373189 1594609937907349549569973)
              ·
                refine ⟨149494681678814020272185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1594609937907349549569973 149494681678814020272185)
                ·
                  rfl

theorem cell20_982597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_982597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982597 prefixEnd_982597 := by exact prefixLift 982597
  have htrace : WordTrace (prefixWord ++ tailWord_982597) baseStart_982597 baseEnd_982597 := by
    simpa [prefixWord, tailWord_982597, baseEnd_982597] using wordTrace_append hprefix tailTrace_982597
  have hstable : (prefixWord ++ tailWord_982597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982597).length < 2 ^ (prefixWord ++ tailWord_982597).sum := by decide
  have hdescent : baseEnd_982597 < baseStart_982597 := by decide
  rcases family_descends (prefixWord ++ tailWord_982597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982666 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_982666 : Nat := 118140960795 + 982666 * 2 ^ 59
def prefixEnd_982666 : Nat := 4983230072969 + 3 ^ 40 * 982666 * 2
def baseEnd_982666 : Nat := 448515538516584487516273

theorem tailTrace_982666 : CollatzResearch.WordTrace tailWord_982666 prefixEnd_982666 448515538516584487516273 := by
  unfold tailWord_982666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8960193364494095709149963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23893848971984255224399901 8960193364494095709149963)
  ·
    refine ⟨13440290046741143563724945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8960193364494095709149963 13440290046741143563724945)
    ·
      refine ⟨10080217535055857672793709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13440290046741143563724945 10080217535055857672793709)
      ·
        refine ⟨3780081575645946627297641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10080217535055857672793709 3780081575645946627297641)
        ·
          refine ⟨2835061181734459970473231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3780081575645946627297641 2835061181734459970473231)
          ·
            refine ⟨4252591772601689955709847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835061181734459970473231 4252591772601689955709847)
            ·
              refine ⟨6378887658902534933564771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252591772601689955709847 6378887658902534933564771)
              ·
                refine ⟨9568331488353802400347157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378887658902534933564771 9568331488353802400347157)
                ·
                  refine ⟨448515538516584487516273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9568331488353802400347157 448515538516584487516273)
                  ·
                    rfl

theorem cell20_982666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_982666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982666 prefixEnd_982666 := by exact prefixLift 982666
  have htrace : WordTrace (prefixWord ++ tailWord_982666) baseStart_982666 baseEnd_982666 := by
    simpa [prefixWord, tailWord_982666, baseEnd_982666] using wordTrace_append hprefix tailTrace_982666
  have hstable : (prefixWord ++ tailWord_982666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982666).length < 2 ^ (prefixWord ++ tailWord_982666).sum := by decide
  have hdescent : baseEnd_982666 < baseStart_982666 := by decide
  rcases family_descends (prefixWord ++ tailWord_982666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982710 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_982710 : Nat := 118140960795 + 982710 * 2 ^ 59
def prefixEnd_982710 : Nat := 4983230072969 + 3 ^ 40 * 982710 * 2
def baseEnd_982710 : Nat := 448535621315515890049427

theorem tailTrace_982710 : CollatzResearch.WordTrace tailWord_982710 prefixEnd_982710 448535621315515890049427 := by
  unfold tailWord_982710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2240148641863561146950099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23894918846544652234134389 2240148641863561146950099)
  ·
    refine ⟨3360222962795341720425149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2240148641863561146950099 3360222962795341720425149)
    ·
      refine ⟨1260083611048253145159431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3360222962795341720425149 1260083611048253145159431)
      ·
        refine ⟨1890125416572379717739147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260083611048253145159431 1890125416572379717739147)
        ·
          refine ⟨2835188124858569576608721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890125416572379717739147 2835188124858569576608721)
          ·
            refine ⟨2126391093643927182456541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2835188124858569576608721 2126391093643927182456541)
            ·
              refine ⟨797396660116472693421203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2126391093643927182456541 797396660116472693421203)
              ·
                refine ⟨1196094990174709040131805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797396660116472693421203 1196094990174709040131805)
                ·
                  refine ⟨448535621315515890049427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196094990174709040131805 448535621315515890049427)
                  ·
                    rfl

theorem cell20_982710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_982710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982710 prefixEnd_982710 := by exact prefixLift 982710
  have htrace : WordTrace (prefixWord ++ tailWord_982710) baseStart_982710 baseEnd_982710 := by
    simpa [prefixWord, tailWord_982710, baseEnd_982710] using wordTrace_append hprefix tailTrace_982710
  have hstable : (prefixWord ++ tailWord_982710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982710).length < 2 ^ (prefixWord ++ tailWord_982710).sum := by decide
  have hdescent : baseEnd_982710 < baseStart_982710 := by decide
  rcases family_descends (prefixWord ++ tailWord_982710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982714 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_982714 : Nat := 118140960795 + 982714 * 2 ^ 59
def prefixEnd_982714 : Nat := 4983230072969 + 3 ^ 40 * 982714 * 2
def baseEnd_982714 : Nat := 448537447024509653916077

theorem tailTrace_982714 : CollatzResearch.WordTrace tailWord_982714 prefixEnd_982714 448537447024509653916077 := by
  unfold tailWord_982714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8960631040450621758586799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23895016107868324689564797 8960631040450621758586799)
  ·
    refine ⟨13440946560675932637880199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8960631040450621758586799 13440946560675932637880199)
    ·
      refine ⟨20161419841013898956820299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13440946560675932637880199 20161419841013898956820299)
      ·
        refine ⟨30242129761520848435230449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20161419841013898956820299 30242129761520848435230449)
        ·
          refine ⟨22681597321140636326422837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30242129761520848435230449 22681597321140636326422837)
          ·
            refine ⟨2126399748856934655602141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22681597321140636326422837 2126399748856934655602141)
            ·
              refine ⟨797399905821350495850803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2126399748856934655602141 797399905821350495850803)
              ·
                refine ⟨1196099858732025743776205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797399905821350495850803 1196099858732025743776205)
                ·
                  refine ⟨448537447024509653916077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196099858732025743776205 448537447024509653916077)
                  ·
                    rfl

theorem cell20_982714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_982714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982714 prefixEnd_982714 := by exact prefixLift 982714
  have htrace : WordTrace (prefixWord ++ tailWord_982714) baseStart_982714 baseEnd_982714 := by
    simpa [prefixWord, tailWord_982714, baseEnd_982714] using wordTrace_append hprefix tailTrace_982714
  have hstable : (prefixWord ++ tailWord_982714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982714).length < 2 ^ (prefixWord ++ tailWord_982714).sum := by decide
  have hdescent : baseEnd_982714 < baseStart_982714 := by decide
  rcases family_descends (prefixWord ++ tailWord_982714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982738 : List Nat := [3, 2, 2, 2, 2, 1, 3, 3, 2]
def baseStart_982738 : Nat := 118140960795 + 982738 * 2 ^ 59
def prefixEnd_982738 : Nat := 4983230072969 + 3 ^ 40 * 982738 * 2
def baseEnd_982738 : Nat := 448548401278472237115979

theorem tailTrace_982738 : CollatzResearch.WordTrace tailWord_982738 prefixEnd_982738 448548401278472237115979 := by
  unfold tailWord_982738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8960849878428884783305217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23895599675810359422147245 8960849878428884783305217)
  ·
    refine ⟨6720637408821663587478913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8960849878428884783305217 6720637408821663587478913)
    ·
      refine ⟨5040478056616247690609185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6720637408821663587478913 5040478056616247690609185)
      ·
        refine ⟨3780358542462185767956889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5040478056616247690609185 3780358542462185767956889)
        ·
          refine ⟨2835268906846639325967667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3780358542462185767956889 2835268906846639325967667)
          ·
            refine ⟨4252903360269958988951501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835268906846639325967667 4252903360269958988951501)
            ·
              refine ⟨1594838760101234620856813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4252903360269958988951501 1594838760101234620856813)
              ·
                refine ⟨598064535037962982821305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1594838760101234620856813 598064535037962982821305)
                ·
                  refine ⟨448548401278472237115979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598064535037962982821305 448548401278472237115979)
                  ·
                    rfl

theorem cell20_982738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_982738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982738 prefixEnd_982738 := by exact prefixLift 982738
  have htrace : WordTrace (prefixWord ++ tailWord_982738) baseStart_982738 baseEnd_982738 := by
    simpa [prefixWord, tailWord_982738, baseEnd_982738] using wordTrace_append hprefix tailTrace_982738
  have hstable : (prefixWord ++ tailWord_982738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982738).length < 2 ^ (prefixWord ++ tailWord_982738).sum := by decide
  have hdescent : baseEnd_982738 < baseStart_982738 := by decide
  rcases family_descends (prefixWord ++ tailWord_982738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982755 : List Nat := [1, 1, 1, 7, 2, 1, 3, 2, 2]
def baseStart_982755 : Nat := 118140960795 + 982755 * 2 ^ 59
def prefixEnd_982755 : Nat := 4983230072969 + 3 ^ 40 * 982755 * 2
def baseEnd_982755 : Nat := 448556160541695733549243

theorem tailTrace_982755 : CollatzResearch.WordTrace tailWord_982755 prefixEnd_982755 448556160541695733549243 := by
  unfold tailWord_982755
  simp only [CollatzResearch.WordTrace]
  refine ⟨35844019554653951036589719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23896013036435967357726479 35844019554653951036589719)
  ·
    refine ⟨53766029331980926554884579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35844019554653951036589719 53766029331980926554884579)
    ·
      refine ⟨80649043997971389832326869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53766029331980926554884579 80649043997971389832326869)
      ·
        refine ⟨1890211968702454449195161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 80649043997971389832326869 1890211968702454449195161)
        ·
          refine ⟨1417658976526840836896371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1890211968702454449195161 1417658976526840836896371)
          ·
            refine ⟨2126488464790261255344557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417658976526840836896371 2126488464790261255344557)
            ·
              refine ⟨797433174296347970754209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2126488464790261255344557 797433174296347970754209)
              ·
                refine ⟨598074880722260978065657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797433174296347970754209 598074880722260978065657)
                ·
                  refine ⟨448556160541695733549243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598074880722260978065657 448556160541695733549243)
                  ·
                    rfl

theorem cell20_982755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 2].length) (baseStart_982755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982755 prefixEnd_982755 := by exact prefixLift 982755
  have htrace : WordTrace (prefixWord ++ tailWord_982755) baseStart_982755 baseEnd_982755 := by
    simpa [prefixWord, tailWord_982755, baseEnd_982755] using wordTrace_append hprefix tailTrace_982755
  have hstable : (prefixWord ++ tailWord_982755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982755).length < 2 ^ (prefixWord ++ tailWord_982755).sum := by decide
  have hdescent : baseEnd_982755 < baseStart_982755 := by decide
  rcases family_descends (prefixWord ++ tailWord_982755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982756 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_982756 : Nat := 118140960795 + 982756 * 2 ^ 59
def prefixEnd_982756 : Nat := 4983230072969 + 3 ^ 40 * 982756 * 2
def baseEnd_982756 : Nat := 448556616968944174515905

theorem tailTrace_982756 : CollatzResearch.WordTrace tailWord_982756 prefixEnd_982756 448556616968944174515905 := by
  unfold tailWord_982756
  simp only [CollatzResearch.WordTrace]
  refine ⟨17922028013825164103688061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23896037351766885471584081 17922028013825164103688061)
  ·
    refine ⟨6720760505184436538883023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17922028013825164103688061 6720760505184436538883023)
    ·
      refine ⟨10081140757776654808324535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6720760505184436538883023 10081140757776654808324535)
      ·
        refine ⟨15121711136664982212486803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10081140757776654808324535 15121711136664982212486803)
        ·
          refine ⟨22682566704997473318730205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15121711136664982212486803 22682566704997473318730205)
          ·
            refine ⟨8505962514374052494523827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22682566704997473318730205 8505962514374052494523827)
            ·
              refine ⟨12758943771561078741785741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8505962514374052494523827 12758943771561078741785741)
              ·
                refine ⟨4784603914335404528169653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12758943771561078741785741 4784603914335404528169653)
                ·
                  refine ⟨448556616968944174515905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4784603914335404528169653 448556616968944174515905)
                  ·
                    rfl

theorem cell20_982756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_982756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982756 prefixEnd_982756 := by exact prefixLift 982756
  have htrace : WordTrace (prefixWord ++ tailWord_982756) baseStart_982756 baseEnd_982756 := by
    simpa [prefixWord, tailWord_982756, baseEnd_982756] using wordTrace_append hprefix tailTrace_982756
  have hstable : (prefixWord ++ tailWord_982756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982756).length < 2 ^ (prefixWord ++ tailWord_982756).sum := by decide
  have hdescent : baseEnd_982756 < baseStart_982756 := by decide
  rcases family_descends (prefixWord ++ tailWord_982756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982818 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_982818 : Nat := 118140960795 + 982818 * 2 ^ 59
def prefixEnd_982818 : Nat := 4983230072969 + 3 ^ 40 * 982818 * 2
def baseEnd_982818 : Nat := 448584915458347514448985

theorem tailTrace_982818 : CollatzResearch.WordTrace tailWord_982818 prefixEnd_982818 448584915458347514448985 := by
  unfold tailWord_982818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8961579338356428199033277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23897544902283808530755405 8961579338356428199033277)
  ·
    refine ⟨3360592251883660574637479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8961579338356428199033277 3360592251883660574637479)
    ·
      refine ⟨5040888377825490861956219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3360592251883660574637479 5040888377825490861956219)
      ·
        refine ⟨7561332566738236292934329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5040888377825490861956219 7561332566738236292934329)
        ·
          refine ⟨5670999425053677219700747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7561332566738236292934329 5670999425053677219700747)
          ·
            refine ⟨8506499137580515829551121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5670999425053677219700747 8506499137580515829551121)
            ·
              refine ⟨6379874353185386872163341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8506499137580515829551121 6379874353185386872163341)
              ·
                refine ⟨2392452882444520077061253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6379874353185386872163341 2392452882444520077061253)
                ·
                  refine ⟨448584915458347514448985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2392452882444520077061253 448584915458347514448985)
                  ·
                    rfl

theorem cell20_982818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_982818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982818 prefixEnd_982818 := by exact prefixLift 982818
  have htrace : WordTrace (prefixWord ++ tailWord_982818) baseStart_982818 baseEnd_982818 := by
    simpa [prefixWord, tailWord_982818, baseEnd_982818] using wordTrace_append hprefix tailTrace_982818
  have hstable : (prefixWord ++ tailWord_982818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982818).length < 2 ^ (prefixWord ++ tailWord_982818).sum := by decide
  have hdescent : baseEnd_982818 < baseStart_982818 := by decide
  rcases family_descends (prefixWord ++ tailWord_982818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982842 : List Nat := [3, 1, 1, 1, 5, 2, 3, 4]
def baseStart_982842 : Nat := 118140960795 + 982842 * 2 ^ 59
def prefixEnd_982842 : Nat := 4983230072969 + 3 ^ 40 * 982842 * 2
def baseEnd_982842 : Nat := 149531956570770032549629

theorem tailTrace_982842 : CollatzResearch.WordTrace tailWord_982842 prefixEnd_982842 149531956570770032549629 := by
  unfold tailWord_982842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8961798176334691223751695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23898128470225843263337853 8961798176334691223751695)
  ·
    refine ⟨13442697264502036835627543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8961798176334691223751695 13442697264502036835627543)
    ·
      refine ⟨20164045896753055253441315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13442697264502036835627543 20164045896753055253441315)
      ·
        refine ⟨30246068845129582880161973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20164045896753055253441315 30246068845129582880161973)
        ·
          refine ⟨2835568954230898395015185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30246068845129582880161973 2835568954230898395015185)
          ·
            refine ⟨2126676715673173796261389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2835568954230898395015185 2126676715673173796261389)
            ·
              refine ⟨797503768377440173598021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2126676715673173796261389 797503768377440173598021)
              ·
                refine ⟨149531956570770032549629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 797503768377440173598021 149531956570770032549629)
                ·
                  rfl

theorem cell20_982842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_982842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982842 prefixEnd_982842 := by exact prefixLift 982842
  have htrace : WordTrace (prefixWord ++ tailWord_982842) baseStart_982842 baseEnd_982842 := by
    simpa [prefixWord, tailWord_982842, baseEnd_982842] using wordTrace_append hprefix tailTrace_982842
  have hstable : (prefixWord ++ tailWord_982842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982842).length < 2 ^ (prefixWord ++ tailWord_982842).sum := by decide
  have hdescent : baseEnd_982842 < baseStart_982842 := by decide
  rcases family_descends (prefixWord ++ tailWord_982842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982866 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_982866 : Nat := 118140960795 + 982866 * 2 ^ 59
def prefixEnd_982866 : Nat := 4983230072969 + 3 ^ 40 * 982866 * 2
def baseEnd_982866 : Nat := 448606823966272680848789

theorem tailTrace_982866 : CollatzResearch.WordTrace tailWord_982866 prefixEnd_982866 448606823966272680848789 := by
  unfold tailWord_982866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8962017014312954248470113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23898712038167877995920301 8962017014312954248470113)
  ·
    refine ⟨6721512760734715686352585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8962017014312954248470113 6721512760734715686352585)
    ·
      refine ⟨5041134570551036764764439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6721512760734715686352585 5041134570551036764764439)
      ·
        refine ⟨7561701855826555147146659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5041134570551036764764439 7561701855826555147146659)
        ·
          refine ⟨11342552783739832720719989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7561701855826555147146659 11342552783739832720719989)
          ·
            refine ⟨1063364323475609317567499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11342552783739832720719989 1063364323475609317567499)
            ·
              refine ⟨1595046485213413976351249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063364323475609317567499 1595046485213413976351249)
              ·
                refine ⟨1196284863910060482263437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595046485213413976351249 1196284863910060482263437)
                ·
                  refine ⟨448606823966272680848789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196284863910060482263437 448606823966272680848789)
                  ·
                    rfl

theorem cell20_982866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_982866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982866 prefixEnd_982866 := by exact prefixLift 982866
  have htrace : WordTrace (prefixWord ++ tailWord_982866) baseStart_982866 baseEnd_982866 := by
    simpa [prefixWord, tailWord_982866, baseEnd_982866] using wordTrace_append hprefix tailTrace_982866
  have hstable : (prefixWord ++ tailWord_982866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982866).length < 2 ^ (prefixWord ++ tailWord_982866).sum := by decide
  have hdescent : baseEnd_982866 < baseStart_982866 := by decide
  rcases family_descends (prefixWord ++ tailWord_982866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982901 : List Nat := [1, 3, 4, 1, 1, 1, 3, 6]
def baseStart_982901 : Nat := 118140960795 + 982901 * 2 ^ 59
def prefixEnd_982901 : Nat := 4983230072969 + 3 ^ 40 * 982901 * 2
def baseEnd_982901 : Nat := 149540932973322704893993

theorem tailTrace_982901 : CollatzResearch.WordTrace tailWord_982901 prefixEnd_982901 149540932973322704893993 := by
  unfold tailWord_982901
  simp only [CollatzResearch.WordTrace]
  refine ⟨35849344612125017971404557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23899563074750011980936371 35849344612125017971404557)
  ·
    refine ⟨13443504229546881739276709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35849344612125017971404557 13443504229546881739276709)
    ·
      refine ⟨2520657043040040326114383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13443504229546881739276709 2520657043040040326114383)
      ·
        refine ⟨3780985564560060489171575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520657043040040326114383 3780985564560060489171575)
        ·
          refine ⟨5671478346840090733757363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3780985564560060489171575 5671478346840090733757363)
          ·
            refine ⟨8507217520260136100636045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5671478346840090733757363 8507217520260136100636045)
            ·
              refine ⟨3190206570097551037738517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8507217520260136100636045 3190206570097551037738517)
              ·
                refine ⟨149540932973322704893993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3190206570097551037738517 149540932973322704893993)
                ·
                  rfl

theorem cell20_982901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_982901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982901 prefixEnd_982901 := by exact prefixLift 982901
  have htrace : WordTrace (prefixWord ++ tailWord_982901) baseStart_982901 baseEnd_982901 := by
    simpa [prefixWord, tailWord_982901, baseEnd_982901] using wordTrace_append hprefix tailTrace_982901
  have hstable : (prefixWord ++ tailWord_982901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982901).length < 2 ^ (prefixWord ++ tailWord_982901).sum := by decide
  have hdescent : baseEnd_982901 < baseStart_982901 := by decide
  rcases family_descends (prefixWord ++ tailWord_982901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982934 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_982934 : Nat := 118140960795 + 982934 * 2 ^ 59
def prefixEnd_982934 : Nat := 4983230072969 + 3 ^ 40 * 982934 * 2
def baseEnd_982934 : Nat := 448637861019166666581845

theorem tailTrace_982934 : CollatzResearch.WordTrace tailWord_982934 prefixEnd_982934 448637861019166666581845 := by
  unfold tailWord_982934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2240659263812841537959741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23900365480670309738237237 2240659263812841537959741)
  ·
    refine ⟨840247223929815576734903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2240659263812841537959741 840247223929815576734903)
    ·
      refine ⟨1260370835894723365102355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840247223929815576734903 1260370835894723365102355)
      ·
        refine ⟨1890556253842085047653533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260370835894723365102355 1890556253842085047653533)
        ·
          refine ⟨708958595190781892870075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1890556253842085047653533 708958595190781892870075)
          ·
            refine ⟨1063437892786172839305113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708958595190781892870075 1063437892786172839305113)
            ·
              refine ⟨797578419589629629478835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063437892786172839305113 797578419589629629478835)
              ·
                refine ⟨1196367629384444444218253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797578419589629629478835 1196367629384444444218253)
                ·
                  refine ⟨448637861019166666581845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196367629384444444218253 448637861019166666581845)
                  ·
                    rfl

theorem cell20_982934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_982934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982934 prefixEnd_982934 := by exact prefixLift 982934
  have htrace : WordTrace (prefixWord ++ tailWord_982934) baseStart_982934 baseEnd_982934 := by
    simpa [prefixWord, tailWord_982934, baseEnd_982934] using wordTrace_append hprefix tailTrace_982934
  have hstable : (prefixWord ++ tailWord_982934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982934).length < 2 ^ (prefixWord ++ tailWord_982934).sum := by decide
  have hdescent : baseEnd_982934 < baseStart_982934 := by decide
  rcases family_descends (prefixWord ++ tailWord_982934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982991 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_982991 : Nat := 118140960795 + 982991 * 2 ^ 59
def prefixEnd_982991 : Nat := 4983230072969 + 3 ^ 40 * 982991 * 2
def baseEnd_982991 : Nat := 448663877372327801681611

theorem tailTrace_982991 : CollatzResearch.WordTrace tailWord_982991 prefixEnd_982991 448663877372327801681611 := by
  unfold tailWord_982991
  simp only [CollatzResearch.WordTrace]
  refine ⟨35852627181798963342180827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23901751454532642228120551 35852627181798963342180827)
  ·
    refine ⟨53778940772698445013271241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35852627181798963342180827 53778940772698445013271241)
    ·
      refine ⟨40334205579523833759953431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53778940772698445013271241 40334205579523833759953431)
      ·
        refine ⟨60501308369285750639930147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40334205579523833759953431 60501308369285750639930147)
        ·
          refine ⟨90751962553928625959895221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60501308369285750639930147 90751962553928625959895221)
          ·
            refine ⟨8507996489430808683740177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90751962553928625959895221 8507996489430808683740177)
            ·
              refine ⟨6380997367073106512805133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8507996489430808683740177 6380997367073106512805133)
              ·
                refine ⟨2392874012652414942301925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6380997367073106512805133 2392874012652414942301925)
                ·
                  refine ⟨448663877372327801681611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2392874012652414942301925 448663877372327801681611)
                  ·
                    rfl

theorem cell20_982991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_982991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_982991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_982991 prefixEnd_982991 := by exact prefixLift 982991
  have htrace : WordTrace (prefixWord ++ tailWord_982991) baseStart_982991 baseEnd_982991 := by
    simpa [prefixWord, tailWord_982991, baseEnd_982991] using wordTrace_append hprefix tailTrace_982991
  have hstable : (prefixWord ++ tailWord_982991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982991).length < 2 ^ (prefixWord ++ tailWord_982991).sum := by decide
  have hdescent : baseEnd_982991 < baseStart_982991 := by decide
  rcases family_descends (prefixWord ++ tailWord_982991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983021 : List Nat := [1, 5, 1, 4, 1, 1, 2, 3, 2]
def baseStart_983021 : Nat := 118140960795 + 983021 * 2 ^ 59
def prefixEnd_983021 : Nat := 4983230072969 + 3 ^ 40 * 983021 * 2
def baseEnd_983021 : Nat := 448677570189781030681489

theorem tailTrace_983021 : CollatzResearch.WordTrace tailWord_983021 prefixEnd_983021 448677570189781030681489 := by
  unfold tailWord_983021
  simp only [CollatzResearch.WordTrace]
  refine ⟨35853721371690278465772917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23902480914460185643848611 35853721371690278465772917)
  ·
    refine ⟨3361286378595963606166211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35853721371690278465772917 3361286378595963606166211)
    ·
      refine ⟨5041929567893945409249317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3361286378595963606166211 5041929567893945409249317)
      ·
        refine ⟨945361793980114764234247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5041929567893945409249317 945361793980114764234247)
        ·
          refine ⟨1418042690970172146351371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945361793980114764234247 1418042690970172146351371)
          ·
            refine ⟨2127064036455258219527057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418042690970172146351371 2127064036455258219527057)
            ·
              refine ⟨1595298027341443664645293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2127064036455258219527057 1595298027341443664645293)
              ·
                refine ⟨598236760253041374241985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1595298027341443664645293 598236760253041374241985)
                ·
                  refine ⟨448677570189781030681489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598236760253041374241985 448677570189781030681489)
                  ·
                    rfl

theorem cell20_983021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_983021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983021 prefixEnd_983021 := by exact prefixLift 983021
  have htrace : WordTrace (prefixWord ++ tailWord_983021) baseStart_983021 baseEnd_983021 := by
    simpa [prefixWord, tailWord_983021, baseEnd_983021] using wordTrace_append hprefix tailTrace_983021
  have hstable : (prefixWord ++ tailWord_983021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983021).length < 2 ^ (prefixWord ++ tailWord_983021).sum := by decide
  have hdescent : baseEnd_983021 < baseStart_983021 := by decide
  rcases family_descends (prefixWord ++ tailWord_983021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983036 : List Nat := [2, 2, 2, 1, 2, 2, 9]
def baseStart_983036 : Nat := 118140960795 + 983036 * 2 ^ 59
def prefixEnd_983036 : Nat := 4983230072969 + 3 ^ 40 * 983036 * 2
def baseEnd_983036 : Nat := 49853824066500849464603

theorem tailTrace_983036 : CollatzResearch.WordTrace tailWord_983036 prefixEnd_983036 49853824066500849464603 := by
  unfold tailWord_983036
  simp only [CollatzResearch.WordTrace]
  refine ⟨17927134233317968013784481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23902845644423957351712641 17927134233317968013784481)
  ·
    refine ⟨13445350674988476010338361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17927134233317968013784481 13445350674988476010338361)
    ·
      refine ⟨10084013006241357007753771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13445350674988476010338361 10084013006241357007753771)
      ·
        refine ⟨15126019509362035511630657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10084013006241357007753771 15126019509362035511630657)
        ·
          refine ⟨11344514632021526633722993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15126019509362035511630657 11344514632021526633722993)
          ·
            refine ⟨8508385974016144975292245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11344514632021526633722993 8508385974016144975292245)
            ·
              refine ⟨49853824066500849464603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8508385974016144975292245 49853824066500849464603)
              ·
                rfl

theorem cell20_983036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 9].length) (baseStart_983036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983036 prefixEnd_983036 := by exact prefixLift 983036
  have htrace : WordTrace (prefixWord ++ tailWord_983036) baseStart_983036 baseEnd_983036 := by
    simpa [prefixWord, tailWord_983036, baseEnd_983036] using wordTrace_append hprefix tailTrace_983036
  have hstable : (prefixWord ++ tailWord_983036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983036).length < 2 ^ (prefixWord ++ tailWord_983036).sum := by decide
  have hdescent : baseEnd_983036 < baseStart_983036 := by decide
  rcases family_descends (prefixWord ++ tailWord_983036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983084 : List Nat := [2, 2, 1, 1, 1, 2, 2, 7, 2]
def baseStart_983084 : Nat := 118140960795 + 983084 * 2 ^ 59
def prefixEnd_983084 : Nat := 4983230072969 + 3 ^ 40 * 983084 * 2
def baseEnd_983084 : Nat := 448706325106432811581231

theorem tailTrace_983084 : CollatzResearch.WordTrace tailWord_983084 prefixEnd_983084 448706325106432811581231 := by
  unfold tailWord_983084
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928009585231020112658153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23904012780308026816877537 17928009585231020112658153)
  ·
    refine ⟨13446007188923265084493615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17928009585231020112658153 13446007188923265084493615)
    ·
      refine ⟨20169010783384897626740423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13446007188923265084493615 20169010783384897626740423)
      ·
        refine ⟨30253516175077346440110635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20169010783384897626740423 30253516175077346440110635)
        ·
          refine ⟨45380274262616019660165953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30253516175077346440110635 45380274262616019660165953)
          ·
            refine ⟨34035205696962014745124465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45380274262616019660165953 34035205696962014745124465)
            ·
              refine ⟨25526404272721511058843349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34035205696962014745124465 25526404272721511058843349)
              ·
                refine ⟨598275100141910415441641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25526404272721511058843349 598275100141910415441641)
                ·
                  refine ⟨448706325106432811581231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598275100141910415441641 448706325106432811581231)
                  ·
                    rfl

theorem cell20_983084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_983084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983084 prefixEnd_983084 := by exact prefixLift 983084
  have htrace : WordTrace (prefixWord ++ tailWord_983084) baseStart_983084 baseEnd_983084 := by
    simpa [prefixWord, tailWord_983084, baseEnd_983084] using wordTrace_append hprefix tailTrace_983084
  have hstable : (prefixWord ++ tailWord_983084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983084).length < 2 ^ (prefixWord ++ tailWord_983084).sum := by decide
  have hdescent : baseEnd_983084 < baseStart_983084 := by decide
  rcases family_descends (prefixWord ++ tailWord_983084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983098 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_983098 : Nat := 118140960795 + 983098 * 2 ^ 59
def prefixEnd_983098 : Nat := 4983230072969 + 3 ^ 40 * 983098 * 2
def baseEnd_983098 : Nat := 448712715087910985114507

theorem tailTrace_983098 : CollatzResearch.WordTrace tailWord_983098 prefixEnd_983098 448712715087910985114507 := by
  unfold tailWord_983098
  simp only [CollatzResearch.WordTrace]
  refine ⟨8964132448102830154081487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23904353194940880410883965 8964132448102830154081487)
  ·
    refine ⟨13446198672154245231122231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8964132448102830154081487 13446198672154245231122231)
    ·
      refine ⟨20169298008231367846683347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13446198672154245231122231 20169298008231367846683347)
      ·
        refine ⟨30253947012347051770025021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20169298008231367846683347 30253947012347051770025021)
        ·
          refine ⟨11345230129630144413759383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30253947012347051770025021 11345230129630144413759383)
          ·
            refine ⟨17017845194445216620639075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11345230129630144413759383 17017845194445216620639075)
            ·
              refine ⟨25526767791667824930958613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17017845194445216620639075 25526767791667824930958613)
              ·
                refine ⟨1196567240234429293638685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25526767791667824930958613 1196567240234429293638685)
                ·
                  refine ⟨448712715087910985114507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196567240234429293638685 448712715087910985114507)
                  ·
                    rfl

theorem cell20_983098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_983098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983098 prefixEnd_983098 := by exact prefixLift 983098
  have htrace : WordTrace (prefixWord ++ tailWord_983098) baseStart_983098 baseEnd_983098 := by
    simpa [prefixWord, tailWord_983098, baseEnd_983098] using wordTrace_append hprefix tailTrace_983098
  have hstable : (prefixWord ++ tailWord_983098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983098).length < 2 ^ (prefixWord ++ tailWord_983098).sum := by decide
  have hdescent : baseEnd_983098 < baseStart_983098 := by decide
  rcases family_descends (prefixWord ++ tailWord_983098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983194 : List Nat := [3, 1, 1, 5, 2, 1, 2, 3, 2]
def baseStart_983194 : Nat := 118140960795 + 983194 * 2 ^ 59
def prefixEnd_983194 : Nat := 4983230072969 + 3 ^ 40 * 983194 * 2
def baseEnd_983194 : Nat := 448756532103761317914115

theorem tailTrace_983194 : CollatzResearch.WordTrace tailWord_983194 prefixEnd_983194 448756532103761317914115 := by
  unfold tailWord_983194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8965007800015882252955159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23906687466709019341213757 8965007800015882252955159)
  ·
    refine ⟨13447511700023823379432739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8965007800015882252955159 13447511700023823379432739)
    ·
      refine ⟨20171267550035735069149109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13447511700023823379432739 20171267550035735069149109)
      ·
        refine ⟨1891056332815850162732729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20171267550035735069149109 1891056332815850162732729)
        ·
          refine ⟨1418292249611887622049547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1891056332815850162732729 1418292249611887622049547)
          ·
            refine ⟨2127438374417831433074321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418292249611887622049547 2127438374417831433074321)
            ·
              refine ⟨1595578780813373574805741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2127438374417831433074321 1595578780813373574805741)
              ·
                refine ⟨598342042805015090552153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1595578780813373574805741 598342042805015090552153)
                ·
                  refine ⟨448756532103761317914115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598342042805015090552153 448756532103761317914115)
                  ·
                    rfl

theorem cell20_983194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_983194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983194 prefixEnd_983194 := by exact prefixLift 983194
  have htrace : WordTrace (prefixWord ++ tailWord_983194) baseStart_983194 baseEnd_983194 := by
    simpa [prefixWord, tailWord_983194, baseEnd_983194] using wordTrace_append hprefix tailTrace_983194
  have hstable : (prefixWord ++ tailWord_983194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983194).length < 2 ^ (prefixWord ++ tailWord_983194).sum := by decide
  have hdescent : baseEnd_983194 < baseStart_983194 := by decide
  rcases family_descends (prefixWord ++ tailWord_983194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983236 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_983236 : Nat := 118140960795 + 983236 * 2 ^ 59
def prefixEnd_983236 : Nat := 4983230072969 + 3 ^ 40 * 983236 * 2
def baseEnd_983236 : Nat := 448775702048195838513943

theorem tailTrace_983236 : CollatzResearch.WordTrace tailWord_983236 prefixEnd_983236 448775702048195838513943 := by
  unfold tailWord_983236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17930781532955685092424781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23907708710607580123233041 17930781532955685092424781)
  ·
    refine ⟨6724043074858381909659293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17930781532955685092424781 6724043074858381909659293)
    ·
      refine ⟨2521516153071893216122235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6724043074858381909659293 2521516153071893216122235)
      ·
        refine ⟨3782274229607839824183353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2521516153071893216122235 3782274229607839824183353)
        ·
          refine ⟨2836705672205879868137515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3782274229607839824183353 2836705672205879868137515)
          ·
            refine ⟨4255058508308819802206273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836705672205879868137515 4255058508308819802206273)
            ·
              refine ⟨3191293881231614851654705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255058508308819802206273 3191293881231614851654705)
              ·
                refine ⟨2393470410923711138741029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191293881231614851654705 2393470410923711138741029)
                ·
                  refine ⟨448775702048195838513943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393470410923711138741029 448775702048195838513943)
                  ·
                    rfl

theorem cell20_983236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_983236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983236 prefixEnd_983236 := by exact prefixLift 983236
  have htrace : WordTrace (prefixWord ++ tailWord_983236) baseStart_983236 baseEnd_983236 := by
    simpa [prefixWord, tailWord_983236, baseEnd_983236] using wordTrace_append hprefix tailTrace_983236
  have hstable : (prefixWord ++ tailWord_983236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983236).length < 2 ^ (prefixWord ++ tailWord_983236).sum := by decide
  have hdescent : baseEnd_983236 < baseStart_983236 := by decide
  rcases family_descends (prefixWord ++ tailWord_983236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983250 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_983250 : Nat := 118140960795 + 983250 * 2 ^ 59
def prefixEnd_983250 : Nat := 4983230072969 + 3 ^ 40 * 983250 * 2
def baseEnd_983250 : Nat := 448782092029674012047219

theorem tailTrace_983250 : CollatzResearch.WordTrace tailWord_983250 prefixEnd_983250 448782092029674012047219 := by
  unfold tailWord_983250
  simp only [CollatzResearch.WordTrace]
  refine ⟨8965518421965162643964801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23908049125240433717239469 8965518421965162643964801)
  ·
    refine ⟨6724138816473871982973601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8965518421965162643964801 6724138816473871982973601)
    ·
      refine ⟨5043104112355403987230201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6724138816473871982973601 5043104112355403987230201)
      ·
        refine ⟨3782328084266552990422651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5043104112355403987230201 3782328084266552990422651)
        ·
          refine ⟨5673492126399829485633977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3782328084266552990422651 5673492126399829485633977)
          ·
            refine ⟨4255119094799872114225483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5673492126399829485633977 4255119094799872114225483)
            ·
              refine ⟨6382678642199808171338225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255119094799872114225483 6382678642199808171338225)
              ·
                refine ⟨4787008981649856128503669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6382678642199808171338225 4787008981649856128503669)
                ·
                  refine ⟨448782092029674012047219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4787008981649856128503669 448782092029674012047219)
                  ·
                    rfl

theorem cell20_983250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_983250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983250 prefixEnd_983250 := by exact prefixLift 983250
  have htrace : WordTrace (prefixWord ++ tailWord_983250) baseStart_983250 baseEnd_983250 := by
    simpa [prefixWord, tailWord_983250, baseEnd_983250] using wordTrace_append hprefix tailTrace_983250
  have hstable : (prefixWord ++ tailWord_983250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983250).length < 2 ^ (prefixWord ++ tailWord_983250).sum := by decide
  have hdescent : baseEnd_983250 < baseStart_983250 := by decide
  rcases family_descends (prefixWord ++ tailWord_983250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983266 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 4]
def baseStart_983266 : Nat := 118140960795 + 983266 * 2 ^ 59
def prefixEnd_983266 : Nat := 4983230072969 + 3 ^ 40 * 983266 * 2
def baseEnd_983266 : Nat := 448789394865649067513821

theorem tailTrace_983266 : CollatzResearch.WordTrace tailWord_983266 prefixEnd_983266 448789394865649067513821 := by
  unfold tailWord_983266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8965664313950671327110413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23908438170535123538961101 8965664313950671327110413)
  ·
    refine ⟨3362124117731501747666405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8965664313950671327110413 3362124117731501747666405)
    ·
      refine ⟨630398272074656577687451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3362124117731501747666405 630398272074656577687451)
      ·
        refine ⟨945597408111984866531177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630398272074656577687451 945597408111984866531177)
        ·
          refine ⟨709198056083988649898383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945597408111984866531177 709198056083988649898383)
          ·
            refine ⟨1063797084125982974847575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709198056083988649898383 1063797084125982974847575)
            ·
              refine ⟨1595695626188974462271363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063797084125982974847575 1595695626188974462271363)
              ·
                refine ⟨2393543439283461693407045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595695626188974462271363 2393543439283461693407045)
                ·
                  refine ⟨448789394865649067513821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393543439283461693407045 448789394865649067513821)
                  ·
                    rfl

theorem cell20_983266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_983266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983266 prefixEnd_983266 := by exact prefixLift 983266
  have htrace : WordTrace (prefixWord ++ tailWord_983266) baseStart_983266 baseEnd_983266 := by
    simpa [prefixWord, tailWord_983266, baseEnd_983266] using wordTrace_append hprefix tailTrace_983266
  have hstable : (prefixWord ++ tailWord_983266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983266).length < 2 ^ (prefixWord ++ tailWord_983266).sum := by decide
  have hdescent : baseEnd_983266 < baseStart_983266 := by decide
  rcases family_descends (prefixWord ++ tailWord_983266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983325 : List Nat := [1, 4, 2, 3, 2, 2, 2, 2, 2]
def baseStart_983325 : Nat := 118140960795 + 983325 * 2 ^ 59
def prefixEnd_983325 : Nat := 4983230072969 + 3 ^ 40 * 983325 * 2
def baseEnd_983325 : Nat := 448816324073307084546913

theorem tailTrace_983325 : CollatzResearch.WordTrace tailWord_983325 prefixEnd_983325 448816324073307084546913 := by
  unfold tailWord_983325
  simp only [CollatzResearch.WordTrace]
  refine ⟨35864809162588938384839429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23909872775059292256559619 35864809162588938384839429)
  ·
    refine ⟨6724651717985425947157393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35864809162588938384839429 6724651717985425947157393)
    ·
      refine ⟨5043488788489069460368045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6724651717985425947157393 5043488788489069460368045)
      ·
        refine ⟨1891308295683401047638017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5043488788489069460368045 1891308295683401047638017)
        ·
          refine ⟨1418481221762550785728513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1891308295683401047638017 1418481221762550785728513)
          ·
            refine ⟨1063860916321913089296385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1418481221762550785728513 1063860916321913089296385)
            ·
              refine ⟨797895687241434816972289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063860916321913089296385 797895687241434816972289)
              ·
                refine ⟨598421765431076112729217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797895687241434816972289 598421765431076112729217)
                ·
                  refine ⟨448816324073307084546913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598421765431076112729217 448816324073307084546913)
                  ·
                    rfl

theorem cell20_983325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_983325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983325 prefixEnd_983325 := by exact prefixLift 983325
  have htrace : WordTrace (prefixWord ++ tailWord_983325) baseStart_983325 baseEnd_983325 := by
    simpa [prefixWord, tailWord_983325, baseEnd_983325] using wordTrace_append hprefix tailTrace_983325
  have hstable : (prefixWord ++ tailWord_983325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983325).length < 2 ^ (prefixWord ++ tailWord_983325).sum := by decide
  have hdescent : baseEnd_983325 < baseStart_983325 := by decide
  rcases family_descends (prefixWord ++ tailWord_983325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983329 : List Nat := [1, 2, 3, 2, 1, 1, 6, 2, 2]
def baseStart_983329 : Nat := 118140960795 + 983329 * 2 ^ 59
def prefixEnd_983329 : Nat := 4983230072969 + 3 ^ 40 * 983329 * 2
def baseEnd_983329 : Nat := 448818149782300848413563

theorem tailTrace_983329 : CollatzResearch.WordTrace tailWord_983329 prefixEnd_983329 448818149782300848413563 := by
  unfold tailWord_983329
  simp only [CollatzResearch.WordTrace]
  refine ⟨35864955054574447067985041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23909970036382964711990027 35864955054574447067985041)
  ·
    refine ⟨26898716290930835300988781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35864955054574447067985041 26898716290930835300988781)
    ·
      refine ⟨10087018609099063237870793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26898716290930835300988781 10087018609099063237870793)
      ·
        refine ⟨7565263956824297428403095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10087018609099063237870793 7565263956824297428403095)
        ·
          refine ⟨11347895935236446142604643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7565263956824297428403095 11347895935236446142604643)
          ·
            refine ⟨17021843902854669213906965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11347895935236446142604643 17021843902854669213906965)
            ·
              refine ⟨797898932946312619401889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17021843902854669213906965 797898932946312619401889)
              ·
                refine ⟨598424199709734464551417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797898932946312619401889 598424199709734464551417)
                ·
                  refine ⟨448818149782300848413563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598424199709734464551417 448818149782300848413563)
                  ·
                    rfl

theorem cell20_983329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_983329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983329 prefixEnd_983329 := by exact prefixLift 983329
  have htrace : WordTrace (prefixWord ++ tailWord_983329) baseStart_983329 baseEnd_983329 := by
    simpa [prefixWord, tailWord_983329, baseEnd_983329] using wordTrace_append hprefix tailTrace_983329
  have hstable : (prefixWord ++ tailWord_983329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983329).length < 2 ^ (prefixWord ++ tailWord_983329).sum := by decide
  have hdescent : baseEnd_983329 < baseStart_983329 := by decide
  rcases family_descends (prefixWord ++ tailWord_983329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983336 : List Nat := [2, 1, 5, 1, 3, 2, 1, 5]
def baseStart_983336 : Nat := 118140960795 + 983336 * 2 ^ 59
def prefixEnd_983336 : Nat := 4983230072969 + 3 ^ 40 * 983336 * 2
def baseEnd_983336 : Nat := 149607114924346645060067

theorem tailTrace_983336 : CollatzResearch.WordTrace tailWord_983336 prefixEnd_983336 149607114924346645060067 := by
  unfold tailWord_983336
  simp only [CollatzResearch.WordTrace]
  refine ⟨17932605182774543631744931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23910140243699391508993241 17932605182774543631744931)
  ·
    refine ⟨26898907774161815447617397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17932605182774543631744931 26898907774161815447617397)
    ·
      refine ⟨2521772603827670198214131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26898907774161815447617397 2521772603827670198214131)
      ·
        refine ⟨3782658905741505297321197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2521772603827670198214131 3782658905741505297321197)
        ·
          refine ⟨1418497089653064486495449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3782658905741505297321197 1418497089653064486495449)
          ·
            refine ⟨1063872817239798364871587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1418497089653064486495449 1063872817239798364871587)
            ·
              refine ⟨1595809225859697547307381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063872817239798364871587 1595809225859697547307381)
              ·
                refine ⟨149607114924346645060067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1595809225859697547307381 149607114924346645060067)
                ·
                  rfl

theorem cell20_983336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_983336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983336 prefixEnd_983336 := by exact prefixLift 983336
  have htrace : WordTrace (prefixWord ++ tailWord_983336) baseStart_983336 baseEnd_983336 := by
    simpa [prefixWord, tailWord_983336, baseEnd_983336] using wordTrace_append hprefix tailTrace_983336
  have hstable : (prefixWord ++ tailWord_983336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983336).length < 2 ^ (prefixWord ++ tailWord_983336).sum := by decide
  have hdescent : baseEnd_983336 < baseStart_983336 := by decide
  rcases family_descends (prefixWord ++ tailWord_983336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983340 : List Nat := [2, 2, 1, 1, 1, 3, 5, 5]
def baseStart_983340 : Nat := 118140960795 + 983340 * 2 ^ 59
def prefixEnd_983340 : Nat := 4983230072969 + 3 ^ 40 * 983340 * 2
def baseEnd_983340 : Nat := 149607723494011233015617

theorem tailTrace_983340 : CollatzResearch.WordTrace tailWord_983340 prefixEnd_983340 149607723494011233015617 := by
  unfold tailWord_983340
  simp only [CollatzResearch.WordTrace]
  refine ⟨17932678128767297973317737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23910237505023063964423649 17932678128767297973317737)
  ·
    refine ⟨13449508596575473479988303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17932678128767297973317737 13449508596575473479988303)
    ·
      refine ⟨20174262894863210219982455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13449508596575473479988303 20174262894863210219982455)
      ·
        refine ⟨30261394342294815329973683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20174262894863210219982455 30261394342294815329973683)
        ·
          refine ⟨45392091513442222994960525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30261394342294815329973683 45392091513442222994960525)
          ·
            refine ⟨17022034317540833623110197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45392091513442222994960525 17022034317540833623110197)
            ·
              refine ⟨1595815717269453152166581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17022034317540833623110197 1595815717269453152166581)
              ·
                refine ⟨149607723494011233015617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1595815717269453152166581 149607723494011233015617)
                ·
                  rfl

theorem cell20_983340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_983340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983340 prefixEnd_983340 := by exact prefixLift 983340
  have htrace : WordTrace (prefixWord ++ tailWord_983340) baseStart_983340 baseEnd_983340 := by
    simpa [prefixWord, tailWord_983340, baseEnd_983340] using wordTrace_append hprefix tailTrace_983340
  have hstable : (prefixWord ++ tailWord_983340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983340).length < 2 ^ (prefixWord ++ tailWord_983340).sum := by decide
  have hdescent : baseEnd_983340 < baseStart_983340 := by decide
  rcases family_descends (prefixWord ++ tailWord_983340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983446 : List Nat := [5, 3, 1, 2, 1, 1, 2, 5]
def baseStart_983446 : Nat := 118140960795 + 983446 * 2 ^ 59
def prefixEnd_983446 : Nat := 4983230072969 + 3 ^ 40 * 983446 * 2
def baseEnd_983446 : Nat := 149623850590122813837695

theorem tailTrace_983446 : CollatzResearch.WordTrace tailWord_983446 prefixEnd_983446 149623850590122813837695 := by
  unfold tailWord_983446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2241826399696911003124637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23912814930100384033329461 2241826399696911003124637)
  ·
    refine ⟨840684899886341626171739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2241826399696911003124637 840684899886341626171739)
    ·
      refine ⟨1261027349829512439257609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840684899886341626171739 1261027349829512439257609)
      ·
        refine ⟨945770512372134329443207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1261027349829512439257609 945770512372134329443207)
        ·
          refine ⟨1418655768558201494164811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945770512372134329443207 1418655768558201494164811)
          ·
            refine ⟨2127983652837302241247217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418655768558201494164811 2127983652837302241247217)
            ·
              refine ⟨1595987739627976680935413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2127983652837302241247217 1595987739627976680935413)
              ·
                refine ⟨149623850590122813837695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1595987739627976680935413 149623850590122813837695)
                ·
                  rfl

theorem cell20_983446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_983446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983446 prefixEnd_983446 := by exact prefixLift 983446
  have htrace : WordTrace (prefixWord ++ tailWord_983446) baseStart_983446 baseEnd_983446 := by
    simpa [prefixWord, tailWord_983446, baseEnd_983446] using wordTrace_append hprefix tailTrace_983446
  have hstable : (prefixWord ++ tailWord_983446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983446).length < 2 ^ (prefixWord ++ tailWord_983446).sum := by decide
  have hdescent : baseEnd_983446 < baseStart_983446 := by decide
  rcases family_descends (prefixWord ++ tailWord_983446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983447 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 4]
def baseStart_983447 : Nat := 118140960795 + 983447 * 2 ^ 59
def prefixEnd_983447 : Nat := 4983230072969 + 3 ^ 40 * 983447 * 2
def baseEnd_983447 : Nat := 448872008197616882479747

theorem tailTrace_983447 : CollatzResearch.WordTrace tailWord_983447 prefixEnd_983447 448872008197616882479747 := by
  unfold tailWord_983447
  simp only [CollatzResearch.WordTrace]
  refine ⟨35869258868146953220780595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23912839245431302147187063 35869258868146953220780595)
  ·
    refine ⟨53803888302220429831170893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35869258868146953220780595 53803888302220429831170893)
    ·
      refine ⟨20176458113332661186689085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53803888302220429831170893 20176458113332661186689085)
      ·
        refine ⟨7566171792499747945008407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20176458113332661186689085 7566171792499747945008407)
        ·
          refine ⟨11349257688749621917512611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7566171792499747945008407 11349257688749621917512611)
          ·
            refine ⟨17023886533124432876268917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11349257688749621917512611 17023886533124432876268917)
            ·
              refine ⟨1595989362480415582150211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17023886533124432876268917 1595989362480415582150211)
              ·
                refine ⟨2393984043720623373225317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595989362480415582150211 2393984043720623373225317)
                ·
                  refine ⟨448872008197616882479747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393984043720623373225317 448872008197616882479747)
                  ·
                    rfl

theorem cell20_983447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_983447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983447 prefixEnd_983447 := by exact prefixLift 983447
  have htrace : WordTrace (prefixWord ++ tailWord_983447) baseStart_983447 baseEnd_983447 := by
    simpa [prefixWord, tailWord_983447, baseEnd_983447] using wordTrace_append hprefix tailTrace_983447
  have hstable : (prefixWord ++ tailWord_983447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983447).length < 2 ^ (prefixWord ++ tailWord_983447).sum := by decide
  have hdescent : baseEnd_983447 < baseStart_983447 := by decide
  rcases family_descends (prefixWord ++ tailWord_983447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983453 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 3]
def baseStart_983453 : Nat := 118140960795 + 983453 * 2 ^ 59
def prefixEnd_983453 : Nat := 4983230072969 + 3 ^ 40 * 983453 * 2
def baseEnd_983453 : Nat := 448874746761107528279723

theorem tailTrace_983453 : CollatzResearch.WordTrace tailWord_983453 prefixEnd_983453 448874746761107528279723 := by
  unfold tailWord_983453
  simp only [CollatzResearch.WordTrace]
  refine ⟨35869477706125216245499013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23912985137416810830332675 35869477706125216245499013)
  ·
    refine ⟨6725527069898478046031065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35869477706125216245499013 6725527069898478046031065)
    ·
      refine ⟨5044145302423858534523299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6725527069898478046031065 5044145302423858534523299)
      ·
        refine ⟨7566217953635787801784949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5044145302423858534523299 7566217953635787801784949)
        ·
          refine ⟨709332933153355106417339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7566217953635787801784949 709332933153355106417339)
          ·
            refine ⟨1063999399730032659626009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709332933153355106417339 1063999399730032659626009)
            ·
              refine ⟨797999549797524494719507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063999399730032659626009 797999549797524494719507)
              ·
                refine ⟨1196999324696286742079261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797999549797524494719507 1196999324696286742079261)
                ·
                  refine ⟨448874746761107528279723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196999324696286742079261 448874746761107528279723)
                  ·
                    rfl

theorem cell20_983453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_983453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983453 prefixEnd_983453 := by exact prefixLift 983453
  have htrace : WordTrace (prefixWord ++ tailWord_983453) baseStart_983453 baseEnd_983453 := by
    simpa [prefixWord, tailWord_983453, baseEnd_983453] using wordTrace_append hprefix tailTrace_983453
  have hstable : (prefixWord ++ tailWord_983453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983453).length < 2 ^ (prefixWord ++ tailWord_983453).sum := by decide
  have hdescent : baseEnd_983453 < baseStart_983453 := by decide
  rcases family_descends (prefixWord ++ tailWord_983453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983468 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_983468 : Nat := 118140960795 + 983468 * 2 ^ 59
def prefixEnd_983468 : Nat := 4983230072969 + 3 ^ 40 * 983468 * 2
def baseEnd_983468 : Nat := 448881593169834142779661

theorem tailTrace_983468 : CollatzResearch.WordTrace tailWord_983468 prefixEnd_983468 448881593169834142779661 := by
  unfold tailWord_983468
  simp only [CollatzResearch.WordTrace]
  refine ⟨17935012400535436903647529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23913349867380582538196705 17935012400535436903647529)
  ·
    refine ⟨13451259300401577677735647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17935012400535436903647529 13451259300401577677735647)
    ·
      refine ⟨20176888950602366516603471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13451259300401577677735647 20176888950602366516603471)
      ·
        refine ⟨30265333425903549774905207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20176888950602366516603471 30265333425903549774905207)
        ·
          refine ⟨45398000138855324662357811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30265333425903549774905207 45398000138855324662357811)
          ·
            refine ⟨68097000208282986993536717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45398000138855324662357811 68097000208282986993536717)
            ·
              refine ⟨25536375078106120122576269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68097000208282986993536717 25536375078106120122576269)
              ·
                refine ⟨9576140654289795045966101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25536375078106120122576269 9576140654289795045966101)
                ·
                  refine ⟨448881593169834142779661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9576140654289795045966101 448881593169834142779661)
                  ·
                    rfl

theorem cell20_983468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_983468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983468 prefixEnd_983468 := by exact prefixLift 983468
  have htrace : WordTrace (prefixWord ++ tailWord_983468) baseStart_983468 baseEnd_983468 := by
    simpa [prefixWord, tailWord_983468, baseEnd_983468] using wordTrace_append hprefix tailTrace_983468
  have hstable : (prefixWord ++ tailWord_983468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983468).length < 2 ^ (prefixWord ++ tailWord_983468).sum := by decide
  have hdescent : baseEnd_983468 < baseStart_983468 := by decide
  rcases family_descends (prefixWord ++ tailWord_983468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983492 : List Nat := [2, 3, 3, 2, 10]
def baseStart_983492 : Nat := 118140960795 + 983492 * 2 ^ 59
def prefixEnd_983492 : Nat := 4983230072969 + 3 ^ 40 * 983492 * 2
def baseEnd_983492 : Nat := 5541883301528354641723

theorem tailTrace_983492 : CollatzResearch.WordTrace tailWord_983492 prefixEnd_983492 5541883301528354641723 := by
  unfold tailWord_983492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17935450076491962953084365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23913933435322617270779153 17935450076491962953084365)
  ·
    refine ⟨6725793778684486107406637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17935450076491962953084365 6725793778684486107406637)
    ·
      refine ⟨2522172667006682290277489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6725793778684486107406637 2522172667006682290277489)
      ·
        refine ⟨1891629500255011717708117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2522172667006682290277489 1891629500255011717708117)
        ·
          refine ⟨5541883301528354641723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1891629500255011717708117 5541883301528354641723)
          ·
            rfl

theorem cell20_983492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 10].length) (baseStart_983492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983492 prefixEnd_983492 := by exact prefixLift 983492
  have htrace : WordTrace (prefixWord ++ tailWord_983492) baseStart_983492 baseEnd_983492 := by
    simpa [prefixWord, tailWord_983492, baseEnd_983492] using wordTrace_append hprefix tailTrace_983492
  have hstable : (prefixWord ++ tailWord_983492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983492).length < 2 ^ (prefixWord ++ tailWord_983492).sum := by decide
  have hdescent : baseEnd_983492 < baseStart_983492 := by decide
  rcases family_descends (prefixWord ++ tailWord_983492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983509 : List Nat := [1, 3, 2, 3, 1, 4, 1, 5]
def baseStart_983509 : Nat := 118140960795 + 983509 * 2 ^ 59
def prefixEnd_983509 : Nat := 4983230072969 + 3 ^ 40 * 983509 * 2
def baseEnd_983509 : Nat := 149633435562340074137609

theorem tailTrace_983509 : CollatzResearch.WordTrace tailWord_983509 prefixEnd_983509 149633435562340074137609 := by
  unfold tailWord_983509
  simp only [CollatzResearch.WordTrace]
  refine ⟨35871520193922337809537581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23914346795948225206358387 35871520193922337809537581)
  ·
    refine ⟨13451820072720876678576593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35871520193922337809537581 13451820072720876678576593)
    ·
      refine ⟨10088865054540657508932445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13451820072720876678576593 10088865054540657508932445)
      ·
        refine ⟨3783324395452746565849667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10088865054540657508932445 3783324395452746565849667)
        ·
          refine ⟨5674986593179119848774501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783324395452746565849667 5674986593179119848774501)
          ·
            refine ⟨1064059986221084971645219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5674986593179119848774501 1064059986221084971645219)
            ·
              refine ⟨1596089979331627457467829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064059986221084971645219 1596089979331627457467829)
              ·
                refine ⟨149633435562340074137609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1596089979331627457467829 149633435562340074137609)
                ·
                  rfl

theorem cell20_983509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 5].length) (baseStart_983509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983509 prefixEnd_983509 := by exact prefixLift 983509
  have htrace : WordTrace (prefixWord ++ tailWord_983509) baseStart_983509 baseEnd_983509 := by
    simpa [prefixWord, tailWord_983509, baseEnd_983509] using wordTrace_append hprefix tailTrace_983509
  have hstable : (prefixWord ++ tailWord_983509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983509).length < 2 ^ (prefixWord ++ tailWord_983509).sum := by decide
  have hdescent : baseEnd_983509 < baseStart_983509 := by decide
  rcases family_descends (prefixWord ++ tailWord_983509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983537 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_983537 : Nat := 118140960795 + 983537 * 2 ^ 59
def prefixEnd_983537 : Nat := 4983230072969 + 3 ^ 40 * 983537 * 2
def baseEnd_983537 : Nat := 448913086649976569479379

theorem tailTrace_983537 : CollatzResearch.WordTrace tailWord_983537 prefixEnd_983537 448913086649976569479379 := by
  unfold tailWord_983537
  simp only [CollatzResearch.WordTrace]
  refine ⟨35872541437820898591556865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23915027625213932394371243 35872541437820898591556865)
  ·
    refine ⟨26904406078365673943667649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35872541437820898591556865 26904406078365673943667649)
    ·
      refine ⟨20178304558774255457750737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26904406078365673943667649 20178304558774255457750737)
      ·
        refine ⟨15133728419080691593313053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20178304558774255457750737 15133728419080691593313053)
        ·
          refine ⟨5675148157155259347492395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15133728419080691593313053 5675148157155259347492395)
          ·
            refine ⟨8512722235732889021238593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675148157155259347492395 8512722235732889021238593)
            ·
              refine ⟨6384541676799666765928945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8512722235732889021238593 6384541676799666765928945)
              ·
                refine ⟨4788406257599750074446709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384541676799666765928945 4788406257599750074446709)
                ·
                  refine ⟨448913086649976569479379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4788406257599750074446709 448913086649976569479379)
                  ·
                    rfl

theorem cell20_983537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_983537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983537 prefixEnd_983537 := by exact prefixLift 983537
  have htrace : WordTrace (prefixWord ++ tailWord_983537) baseStart_983537 baseEnd_983537 := by
    simpa [prefixWord, tailWord_983537, baseEnd_983537] using wordTrace_append hprefix tailTrace_983537
  have hstable : (prefixWord ++ tailWord_983537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983537).length < 2 ^ (prefixWord ++ tailWord_983537).sum := by decide
  have hdescent : baseEnd_983537 < baseStart_983537 := by decide
  rcases family_descends (prefixWord ++ tailWord_983537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983544 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_983544 : Nat := 118140960795 + 983544 * 2 ^ 59
def prefixEnd_983544 : Nat := 4983230072969 + 3 ^ 40 * 983544 * 2
def baseEnd_983544 : Nat := 448916281640715656246017

theorem tailTrace_983544 : CollatzResearch.WordTrace tailWord_983544 prefixEnd_983544 448916281640715656246017 := by
  unfold tailWord_983544
  simp only [CollatzResearch.WordTrace]
  refine ⟨17936398374397769393530843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23915197832530359191374457 17936398374397769393530843)
  ·
    refine ⟨26904597561596654090296265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17936398374397769393530843 26904597561596654090296265)
    ·
      refine ⟨20178448171197490567722199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26904597561596654090296265 20178448171197490567722199)
      ·
        refine ⟨30267672256796235851583299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20178448171197490567722199 30267672256796235851583299)
        ·
          refine ⟨45401508385194353777374949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30267672256796235851583299 45401508385194353777374949)
          ·
            refine ⟨8512782822223941333257803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45401508385194353777374949 8512782822223941333257803)
            ·
              refine ⟨12769174233335911999886705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8512782822223941333257803 12769174233335911999886705)
              ·
                refine ⟨9576880675001933999915029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12769174233335911999886705 9576880675001933999915029)
                ·
                  refine ⟨448916281640715656246017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9576880675001933999915029 448916281640715656246017)
                  ·
                    rfl

theorem cell20_983544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_983544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983544 prefixEnd_983544 := by exact prefixLift 983544
  have htrace : WordTrace (prefixWord ++ tailWord_983544) baseStart_983544 baseEnd_983544 := by
    simpa [prefixWord, tailWord_983544, baseEnd_983544] using wordTrace_append hprefix tailTrace_983544
  have hstable : (prefixWord ++ tailWord_983544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983544).length < 2 ^ (prefixWord ++ tailWord_983544).sum := by decide
  have hdescent : baseEnd_983544 < baseStart_983544 := by decide
  rcases family_descends (prefixWord ++ tailWord_983544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983551 : List Nat := [1, 1, 2, 2, 1, 2, 11]
def baseStart_983551 : Nat := 118140960795 + 983551 * 2 ^ 59
def prefixEnd_983551 : Nat := 4983230072969 + 3 ^ 40 * 983551 * 2
def baseEnd_983551 : Nat := 49879941847939415890295

theorem tailTrace_983551 : CollatzResearch.WordTrace tailWord_983551 prefixEnd_983551 49879941847939415890295 := by
  unfold tailWord_983551
  simp only [CollatzResearch.WordTrace]
  refine ⟨35873052059770178982566507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23915368039846785988377671 35873052059770178982566507)
  ·
    refine ⟨53809578089655268473849761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35873052059770178982566507 53809578089655268473849761)
    ·
      refine ⟨40357183567241451355387321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53809578089655268473849761 40357183567241451355387321)
      ·
        refine ⟨30267887675431088516540491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40357183567241451355387321 30267887675431088516540491)
        ·
          refine ⟨45401831513146632774810737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30267887675431088516540491 45401831513146632774810737)
          ·
            refine ⟨34051373634859974581108053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45401831513146632774810737 34051373634859974581108053)
            ·
              refine ⟨49879941847939415890295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34051373634859974581108053 49879941847939415890295)
              ·
                rfl

theorem cell20_983551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 11].length) (baseStart_983551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983551 prefixEnd_983551 := by exact prefixLift 983551
  have htrace : WordTrace (prefixWord ++ tailWord_983551) baseStart_983551 baseEnd_983551 := by
    simpa [prefixWord, tailWord_983551, baseEnd_983551] using wordTrace_append hprefix tailTrace_983551
  have hstable : (prefixWord ++ tailWord_983551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983551).length < 2 ^ (prefixWord ++ tailWord_983551).sum := by decide
  have hdescent : baseEnd_983551 < baseStart_983551 := by decide
  rcases family_descends (prefixWord ++ tailWord_983551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983591 : List Nat := [1, 1, 7, 2, 1, 2, 1, 3, 2]
def baseStart_983591 : Nat := 118140960795 + 983591 * 2 ^ 59
def prefixEnd_983591 : Nat := 4983230072969 + 3 ^ 40 * 983591 * 2
def baseEnd_983591 : Nat := 448937733721392381679159

theorem tailTrace_983591 : CollatzResearch.WordTrace tailWord_983591 prefixEnd_983591 448937733721392381679159 := by
  unfold tailWord_983591
  simp only [CollatzResearch.WordTrace]
  refine ⟨35874510979625265814022627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23916340653083510542681751 35874510979625265814022627)
  ·
    refine ⟨53811766469437898721033941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35874510979625265814022627 53811766469437898721033941)
    ·
      refine ⟨1261213276627450751274233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 53811766469437898721033941 1261213276627450751274233)
      ·
        refine ⟨945909957470588063455675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1261213276627450751274233 945909957470588063455675)
        ·
          refine ⟨1418864936205882095183513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945909957470588063455675 1418864936205882095183513)
          ·
            refine ⟨1064148702154411571387635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1418864936205882095183513 1064148702154411571387635)
            ·
              refine ⟨1596223053231617357081453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064148702154411571387635 1596223053231617357081453)
              ·
                refine ⟨598583644961856508905545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1596223053231617357081453 598583644961856508905545)
                ·
                  refine ⟨448937733721392381679159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598583644961856508905545 448937733721392381679159)
                  ·
                    rfl

theorem cell20_983591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 2].length) (baseStart_983591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983591 prefixEnd_983591 := by exact prefixLift 983591
  have htrace : WordTrace (prefixWord ++ tailWord_983591) baseStart_983591 baseEnd_983591 := by
    simpa [prefixWord, tailWord_983591, baseEnd_983591] using wordTrace_append hprefix tailTrace_983591
  have hstable : (prefixWord ++ tailWord_983591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983591).length < 2 ^ (prefixWord ++ tailWord_983591).sum := by decide
  have hdescent : baseEnd_983591 < baseStart_983591 := by decide
  rcases family_descends (prefixWord ++ tailWord_983591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983592 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_983592 : Nat := 118140960795 + 983592 * 2 ^ 59
def prefixEnd_983592 : Nat := 4983230072969 + 3 ^ 40 * 983592 * 2
def baseEnd_983592 : Nat := 448938190148640822645821

theorem tailTrace_983592 : CollatzResearch.WordTrace tailWord_983592 prefixEnd_983592 448938190148640822645821 := by
  unfold tailWord_983592
  simp only [CollatzResearch.WordTrace]
  refine ⟨17937273726310821492404515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23916364968414428656539353 17937273726310821492404515)
  ·
    refine ⟨26905910589466232238606773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17937273726310821492404515 26905910589466232238606773)
    ·
      refine ⟨2522429117762459272369385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26905910589466232238606773 2522429117762459272369385)
      ·
        refine ⟨1891821838321844454277039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2522429117762459272369385 1891821838321844454277039)
        ·
          refine ⟨2837732757482766681415559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891821838321844454277039 2837732757482766681415559)
          ·
            refine ⟨4256599136224150022123339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837732757482766681415559 4256599136224150022123339)
            ·
              refine ⟨6384898704336225033185009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256599136224150022123339 6384898704336225033185009)
              ·
                refine ⟨4788674028252168774888757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384898704336225033185009 4788674028252168774888757)
                ·
                  refine ⟨448938190148640822645821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4788674028252168774888757 448938190148640822645821)
                  ·
                    rfl

theorem cell20_983592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_983592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983592 prefixEnd_983592 := by exact prefixLift 983592
  have htrace : WordTrace (prefixWord ++ tailWord_983592) baseStart_983592 baseEnd_983592 := by
    simpa [prefixWord, tailWord_983592, baseEnd_983592] using wordTrace_append hprefix tailTrace_983592
  have hstable : (prefixWord ++ tailWord_983592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983592).length < 2 ^ (prefixWord ++ tailWord_983592).sum := by decide
  have hdescent : baseEnd_983592 < baseStart_983592 := by decide
  rcases family_descends (prefixWord ++ tailWord_983592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983627 : List Nat := [1, 1, 1, 1, 3, 1, 5, 7]
def baseStart_983627 : Nat := 118140960795 + 983627 * 2 ^ 59
def prefixEnd_983627 : Nat := 4983230072969 + 3 ^ 40 * 983627 * 2
def baseEnd_983627 : Nat := 149651388367445418826337

theorem tailTrace_983627 : CollatzResearch.WordTrace tailWord_983627 prefixEnd_983627 149651388367445418826337 := by
  unfold tailWord_983627
  simp only [CollatzResearch.WordTrace]
  refine ⟨35875824007494843962333135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23917216004996562641555423 35875824007494843962333135)
  ·
    refine ⟨53813736011242265943499703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35875824007494843962333135 53813736011242265943499703)
    ·
      refine ⟨80720604016863398915249555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53813736011242265943499703 80720604016863398915249555)
      ·
        refine ⟨121080906025295098372874333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80720604016863398915249555 121080906025295098372874333)
        ·
          refine ⟨45405339759485661889827875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121080906025295098372874333 45405339759485661889827875)
          ·
            refine ⟨68108009639228492834741813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45405339759485661889827875 68108009639228492834741813)
            ·
              refine ⟨6385125903677671203257045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68108009639228492834741813 6385125903677671203257045)
              ·
                refine ⟨149651388367445418826337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6385125903677671203257045 149651388367445418826337)
                ·
                  rfl

theorem cell20_983627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_983627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983627 prefixEnd_983627 := by exact prefixLift 983627
  have htrace : WordTrace (prefixWord ++ tailWord_983627) baseStart_983627 baseEnd_983627 := by
    simpa [prefixWord, tailWord_983627, baseEnd_983627] using wordTrace_append hprefix tailTrace_983627
  have hstable : (prefixWord ++ tailWord_983627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983627).length < 2 ^ (prefixWord ++ tailWord_983627).sum := by decide
  have hdescent : baseEnd_983627 < baseStart_983627 := by decide
  rcases family_descends (prefixWord ++ tailWord_983627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983719 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 3]
def baseStart_983719 : Nat := 118140960795 + 983719 * 2 ^ 59
def prefixEnd_983719 : Nat := 4983230072969 + 3 ^ 40 * 983719 * 2
def baseEnd_983719 : Nat := 448996156409192825411969

theorem tailTrace_983719 : CollatzResearch.WordTrace tailWord_983719 prefixEnd_983719 448996156409192825411969 := by
  unfold tailWord_983719
  simp only [CollatzResearch.WordTrace]
  refine ⟨35879179523161543674682211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23919453015441029116454807 35879179523161543674682211)
  ·
    refine ⟨53818769284742315512023317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35879179523161543674682211 53818769284742315512023317)
    ·
      refine ⟨2522754810222296039626093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53818769284742315512023317 2522754810222296039626093)
      ·
        refine ⟨946033053833361014859785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2522754810222296039626093 946033053833361014859785)
        ·
          refine ⟨709524790375020761144839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946033053833361014859785 709524790375020761144839)
          ·
            refine ⟨1064287185562531141717259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709524790375020761144839 1064287185562531141717259)
            ·
              refine ⟨1596430778343796712575889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064287185562531141717259 1596430778343796712575889)
              ·
                refine ⟨1197323083757847534431917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596430778343796712575889 1197323083757847534431917)
                ·
                  refine ⟨448996156409192825411969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197323083757847534431917 448996156409192825411969)
                  ·
                    rfl

theorem cell20_983719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 3].length) (baseStart_983719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983719 prefixEnd_983719 := by exact prefixLift 983719
  have htrace : WordTrace (prefixWord ++ tailWord_983719) baseStart_983719 baseEnd_983719 := by
    simpa [prefixWord, tailWord_983719, baseEnd_983719] using wordTrace_append hprefix tailTrace_983719
  have hstable : (prefixWord ++ tailWord_983719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983719).length < 2 ^ (prefixWord ++ tailWord_983719).sum := by decide
  have hdescent : baseEnd_983719 < baseStart_983719 := by decide
  rcases family_descends (prefixWord ++ tailWord_983719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983727 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 5]
def baseStart_983727 : Nat := 118140960795 + 983727 * 2 ^ 59
def prefixEnd_983727 : Nat := 4983230072969 + 3 ^ 40 * 983727 * 2
def baseEnd_983727 : Nat := 448999807827180353145269

theorem tailTrace_983727 : CollatzResearch.WordTrace tailWord_983727 prefixEnd_983727 448999807827180353145269 := by
  unfold tailWord_983727
  simp only [CollatzResearch.WordTrace]
  refine ⟨35879471307132561040973435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23919647538088374027315623 35879471307132561040973435)
  ·
    refine ⟨53819206960698841561460153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35879471307132561040973435 53819206960698841561460153)
    ·
      refine ⟨40364405220524131171095115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53819206960698841561460153 40364405220524131171095115)
      ·
        refine ⟨60546607830786196756642673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40364405220524131171095115 60546607830786196756642673)
        ·
          refine ⟨45409955873089647567482005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60546607830786196756642673 45409955873089647567482005)
          ·
            refine ⟨2128591681551077229725719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45409955873089647567482005 2128591681551077229725719)
            ·
              refine ⟨3192887522326615844588579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128591681551077229725719 3192887522326615844588579)
              ·
                refine ⟨4789331283489923766882869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192887522326615844588579 4789331283489923766882869)
                ·
                  refine ⟨448999807827180353145269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4789331283489923766882869 448999807827180353145269)
                  ·
                    rfl

theorem cell20_983727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_983727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983727 prefixEnd_983727 := by exact prefixLift 983727
  have htrace : WordTrace (prefixWord ++ tailWord_983727) baseStart_983727 baseEnd_983727 := by
    simpa [prefixWord, tailWord_983727, baseEnd_983727] using wordTrace_append hprefix tailTrace_983727
  have hstable : (prefixWord ++ tailWord_983727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983727).length < 2 ^ (prefixWord ++ tailWord_983727).sum := by decide
  have hdescent : baseEnd_983727 < baseStart_983727 := by decide
  rcases family_descends (prefixWord ++ tailWord_983727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983750 : List Nat := [6, 1, 2, 1, 2, 2, 2, 4]
def baseStart_983750 : Nat := 118140960795 + 983750 * 2 ^ 59
def prefixEnd_983750 : Nat := 4983230072969 + 3 ^ 40 * 983750 * 2
def baseEnd_983750 : Nat := 149670101884631498459503

theorem tailTrace_983750 : CollatzResearch.WordTrace tailWord_983750 prefixEnd_983750 149670101884631498459503 := by
  unfold tailWord_983750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1121259693314038624033147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23920206790699490646040469 1121259693314038624033147)
  ·
    refine ⟨1681889539971057936049721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1121259693314038624033147 1681889539971057936049721)
    ·
      refine ⟨1261417154978293452037291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1681889539971057936049721 1261417154978293452037291)
      ·
        refine ⟨1892125732467440178055937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1261417154978293452037291 1892125732467440178055937)
        ·
          refine ⟨1419094299350580133541953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1892125732467440178055937 1419094299350580133541953)
          ·
            refine ⟨1064320724512935100156465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1419094299350580133541953 1064320724512935100156465)
            ·
              refine ⟨798240543384701325117349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064320724512935100156465 798240543384701325117349)
              ·
                refine ⟨149670101884631498459503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 798240543384701325117349 149670101884631498459503)
                ·
                  rfl

theorem cell20_983750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_983750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983750 prefixEnd_983750 := by exact prefixLift 983750
  have htrace : WordTrace (prefixWord ++ tailWord_983750) baseStart_983750 baseEnd_983750 := by
    simpa [prefixWord, tailWord_983750, baseEnd_983750] using wordTrace_append hprefix tailTrace_983750
  have hstable : (prefixWord ++ tailWord_983750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983750).length < 2 ^ (prefixWord ++ tailWord_983750).sum := by decide
  have hdescent : baseEnd_983750 < baseStart_983750 := by decide
  rcases family_descends (prefixWord ++ tailWord_983750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983758 : List Nat := [4, 1, 1, 1, 3, 3, 1, 6]
def baseStart_983758 : Nat := 118140960795 + 983758 * 2 ^ 59
def prefixEnd_983758 : Nat := 4983230072969 + 3 ^ 40 * 983758 * 2
def baseEnd_983758 : Nat := 149671319023960674370603

theorem tailTrace_983758 : CollatzResearch.WordTrace tailWord_983758 prefixEnd_983758 149671319023960674370603 := by
  unfold tailWord_983758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4485075246252531666918991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23920401313346835556901285 4485075246252531666918991)
  ·
    refine ⟨6727612869378797500378487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4485075246252531666918991 6727612869378797500378487)
    ·
      refine ⟨10091419304068196250567731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6727612869378797500378487 10091419304068196250567731)
      ·
        refine ⟨15137128956102294375851597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10091419304068196250567731 15137128956102294375851597)
        ·
          refine ⟨5676423358538360390944349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15137128956102294375851597 5676423358538360390944349)
          ·
            refine ⟨2128658759451885146604131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5676423358538360390944349 2128658759451885146604131)
            ·
              refine ⟨3192988139177827719906197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128658759451885146604131 3192988139177827719906197)
              ·
                refine ⟨149671319023960674370603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3192988139177827719906197 149671319023960674370603)
                ·
                  rfl

theorem cell20_983758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_983758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983758 prefixEnd_983758 := by exact prefixLift 983758
  have htrace : WordTrace (prefixWord ++ tailWord_983758) baseStart_983758 baseEnd_983758 := by
    simpa [prefixWord, tailWord_983758, baseEnd_983758] using wordTrace_append hprefix tailTrace_983758
  have hstable : (prefixWord ++ tailWord_983758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983758).length < 2 ^ (prefixWord ++ tailWord_983758).sum := by decide
  have hdescent : baseEnd_983758 < baseStart_983758 := by decide
  rcases family_descends (prefixWord ++ tailWord_983758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983764 : List Nat := [2, 4, 1, 3, 2, 2, 1, 3, 2]
def baseStart_983764 : Nat := 118140960795 + 983764 * 2 ^ 59
def prefixEnd_983764 : Nat := 4983230072969 + 3 ^ 40 * 983764 * 2
def baseEnd_983764 : Nat := 449016695635372668911785

theorem tailTrace_983764 : CollatzResearch.WordTrace tailWord_983764 prefixEnd_983764 449016695635372668911785 := by
  unfold tailWord_983764
  simp only [CollatzResearch.WordTrace]
  refine ⟨17940410403999258180035173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23920547205332344240046897 17940410403999258180035173)
  ·
    refine ⟨3363826950749860908756595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17940410403999258180035173 3363826950749860908756595)
    ·
      refine ⟨5045740426124791363134893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3363826950749860908756595 5045740426124791363134893)
      ·
        refine ⟨1892152659796796761175585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5045740426124791363134893 1892152659796796761175585)
        ·
          refine ⟨1419114494847597570881689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1892152659796796761175585 1419114494847597570881689)
          ·
            refine ⟨1064335871135698178161267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1419114494847597570881689 1064335871135698178161267)
            ·
              refine ⟨1596503806703547267241901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064335871135698178161267 1596503806703547267241901)
              ·
                refine ⟨598688927513830225215713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1596503806703547267241901 598688927513830225215713)
                ·
                  refine ⟨449016695635372668911785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598688927513830225215713 449016695635372668911785)
                  ·
                    rfl

theorem cell20_983764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_983764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983764 prefixEnd_983764 := by exact prefixLift 983764
  have htrace : WordTrace (prefixWord ++ tailWord_983764) baseStart_983764 baseEnd_983764 := by
    simpa [prefixWord, tailWord_983764, baseEnd_983764] using wordTrace_append hprefix tailTrace_983764
  have hstable : (prefixWord ++ tailWord_983764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983764).length < 2 ^ (prefixWord ++ tailWord_983764).sum := by decide
  have hdescent : baseEnd_983764 < baseStart_983764 := by decide
  rcases family_descends (prefixWord ++ tailWord_983764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983768 : List Nat := [2, 1, 2, 2, 3, 2, 3, 3, 2]
def baseStart_983768 : Nat := 118140960795 + 983768 * 2 ^ 59
def prefixEnd_983768 : Nat := 4983230072969 + 3 ^ 40 * 983768 * 2
def baseEnd_983768 : Nat := 449018521344366432778435

theorem tailTrace_983768 : CollatzResearch.WordTrace tailWord_983768 prefixEnd_983768 449018521344366432778435 := by
  unfold tailWord_983768
  simp only [CollatzResearch.WordTrace]
  refine ⟨17940483349992012521607979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23920644466656016695477305 17940483349992012521607979)
  ·
    refine ⟨26910725024988018782411969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17940483349992012521607979 26910725024988018782411969)
    ·
      refine ⟨20183043768741014086808977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26910725024988018782411969 20183043768741014086808977)
      ·
        refine ⟨15137282826555760565106733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20183043768741014086808977 15137282826555760565106733)
        ·
          refine ⟨5676481059958410211915025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15137282826555760565106733 5676481059958410211915025)
          ·
            refine ⟨4257360794968807658936269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5676481059958410211915025 4257360794968807658936269)
            ·
              refine ⟨1596510298113302872101101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4257360794968807658936269 1596510298113302872101101)
              ·
                refine ⟨598691361792488577037913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1596510298113302872101101 598691361792488577037913)
                ·
                  refine ⟨449018521344366432778435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598691361792488577037913 449018521344366432778435)
                  ·
                    rfl

theorem cell20_983768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_983768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983768 prefixEnd_983768 := by exact prefixLift 983768
  have htrace : WordTrace (prefixWord ++ tailWord_983768) baseStart_983768 baseEnd_983768 := by
    simpa [prefixWord, tailWord_983768, baseEnd_983768] using wordTrace_append hprefix tailTrace_983768
  have hstable : (prefixWord ++ tailWord_983768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983768).length < 2 ^ (prefixWord ++ tailWord_983768).sum := by decide
  have hdescent : baseEnd_983768 < baseStart_983768 := by decide
  rcases family_descends (prefixWord ++ tailWord_983768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983817 : List Nat := [1, 2, 1, 1, 3, 2, 4, 6]
def baseStart_983817 : Nat := 118140960795 + 983817 * 2 ^ 59
def prefixEnd_983817 : Nat := 4983230072969 + 3 ^ 40 * 983817 * 2
def baseEnd_983817 : Nat := 149680295426513346714967

theorem tailTrace_983817 : CollatzResearch.WordTrace tailWord_983817 prefixEnd_983817 149680295426513346714967 := by
  unfold tailWord_983817
  simp only [CollatzResearch.WordTrace]
  refine ⟨35882753876806506411749705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23921835917871004274499803 35882753876806506411749705)
  ·
    refine ⟨26912065407604879808812279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35882753876806506411749705 26912065407604879808812279)
    ·
      refine ⟨40368098111407319713218419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26912065407604879808812279 40368098111407319713218419)
      ·
        refine ⟨60552147167110979569827629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40368098111407319713218419 60552147167110979569827629)
        ·
          refine ⟨22707055187666617338685361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60552147167110979569827629 22707055187666617338685361)
          ·
            refine ⟨17030291390749963004014021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22707055187666617338685361 17030291390749963004014021)
            ·
              refine ⟨3193179635765618063252629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17030291390749963004014021 3193179635765618063252629)
              ·
                refine ⟨149680295426513346714967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3193179635765618063252629 149680295426513346714967)
                ·
                  rfl

theorem cell20_983817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_983817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983817 prefixEnd_983817 := by exact prefixLift 983817
  have htrace : WordTrace (prefixWord ++ tailWord_983817) baseStart_983817 baseEnd_983817 := by
    simpa [prefixWord, tailWord_983817, baseEnd_983817] using wordTrace_append hprefix tailTrace_983817
  have hstable : (prefixWord ++ tailWord_983817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983817).length < 2 ^ (prefixWord ++ tailWord_983817).sum := by decide
  have hdescent : baseEnd_983817 < baseStart_983817 := by decide
  rcases family_descends (prefixWord ++ tailWord_983817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983827 : List Nat := [1, 1, 1, 2, 1, 3, 4, 5, 2]
def baseStart_983827 : Nat := 118140960795 + 983827 * 2 ^ 59
def prefixEnd_983827 : Nat := 4983230072969 + 3 ^ 40 * 983827 * 2
def baseEnd_983827 : Nat := 449045450552024449811527

theorem tailTrace_983827 : CollatzResearch.WordTrace tailWord_983827 prefixEnd_983827 449045450552024449811527 := by
  unfold tailWord_983827
  simp only [CollatzResearch.WordTrace]
  refine ⟨35883118606770278119613735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23922079071180185413075823 35883118606770278119613735)
  ·
    refine ⟨53824677910155417179420603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35883118606770278119613735 53824677910155417179420603)
    ·
      refine ⟨80737016865233125769130905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53824677910155417179420603 80737016865233125769130905)
      ·
        refine ⟨60552762648924844326848179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80737016865233125769130905 60552762648924844326848179)
        ·
          refine ⟨90829143973387266490272269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60552762648924844326848179 90829143973387266490272269)
          ·
            refine ⟨34060928990020224933852101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90829143973387266490272269 34060928990020224933852101)
            ·
              refine ⟨6386424185628792175097269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34060928990020224933852101 6386424185628792175097269)
              ·
                refine ⟨598727267402699266415369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6386424185628792175097269 598727267402699266415369)
                ·
                  refine ⟨449045450552024449811527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598727267402699266415369 449045450552024449811527)
                  ·
                    rfl

theorem cell20_983827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 2].length) (baseStart_983827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983827 prefixEnd_983827 := by exact prefixLift 983827
  have htrace : WordTrace (prefixWord ++ tailWord_983827) baseStart_983827 baseEnd_983827 := by
    simpa [prefixWord, tailWord_983827, baseEnd_983827] using wordTrace_append hprefix tailTrace_983827
  have hstable : (prefixWord ++ tailWord_983827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983827).length < 2 ^ (prefixWord ++ tailWord_983827).sum := by decide
  have hdescent : baseEnd_983827 < baseStart_983827 := by decide
  rcases family_descends (prefixWord ++ tailWord_983827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983892 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 3]
def baseStart_983892 : Nat := 118140960795 + 983892 * 2 ^ 59
def prefixEnd_983892 : Nat := 4983230072969 + 3 ^ 40 * 983892 * 2
def baseEnd_983892 : Nat := 449075118323173112644595

theorem tailTrace_983892 : CollatzResearch.WordTrace tailWord_983892 prefixEnd_983892 449075118323173112644595 := by
  unfold tailWord_983892
  simp only [CollatzResearch.WordTrace]
  refine ⟨17942744675767397110364965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23923659567689862813819953 17942744675767397110364965)
  ·
    refine ⟨3364264626706386958193431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17942744675767397110364965 3364264626706386958193431)
    ·
      refine ⟨5046396940059580437290147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3364264626706386958193431 5046396940059580437290147)
      ·
        refine ⟨7569595410089370655935221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5046396940059580437290147 7569595410089370655935221)
        ·
          refine ⟨709649569695878498993927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7569595410089370655935221 709649569695878498993927)
          ·
            refine ⟨1064474354543817748490891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709649569695878498993927 1064474354543817748490891)
            ·
              refine ⟨1596711531815726622736337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064474354543817748490891 1596711531815726622736337)
              ·
                refine ⟨1197533648861794967052253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596711531815726622736337 1197533648861794967052253)
                ·
                  refine ⟨449075118323173112644595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197533648861794967052253 449075118323173112644595)
                  ·
                    rfl

theorem cell20_983892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_983892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983892 prefixEnd_983892 := by exact prefixLift 983892
  have htrace : WordTrace (prefixWord ++ tailWord_983892) baseStart_983892 baseEnd_983892 := by
    simpa [prefixWord, tailWord_983892, baseEnd_983892] using wordTrace_append hprefix tailTrace_983892
  have hstable : (prefixWord ++ tailWord_983892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983892).length < 2 ^ (prefixWord ++ tailWord_983892).sum := by decide
  have hdescent : baseEnd_983892 < baseStart_983892 := by decide
  rcases family_descends (prefixWord ++ tailWord_983892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983893 : List Nat := [1, 3, 2, 2, 2, 1, 9]
def baseStart_983893 : Nat := 118140960795 + 983893 * 2 ^ 59
def prefixEnd_983893 : Nat := 4983230072969 + 3 ^ 40 * 983893 * 2
def baseEnd_983893 : Nat := 49897286083380172623473

theorem tailTrace_983893 : CollatzResearch.WordTrace tailWord_983893 prefixEnd_983893 49897286083380172623473 := by
  unfold tailWord_983893
  simp only [CollatzResearch.WordTrace]
  refine ⟨35885525824531171391516333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23923683883020780927677555 35885525824531171391516333)
  ·
    refine ⟨13457072184199189271818625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35885525824531171391516333 13457072184199189271818625)
    ·
      refine ⟨10092804138149391953863969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13457072184199189271818625 10092804138149391953863969)
      ·
        refine ⟨7569603103612043965397977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10092804138149391953863969 7569603103612043965397977)
        ·
          refine ⟨5677202327709032974048483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7569603103612043965397977 5677202327709032974048483)
          ·
            refine ⟨8515803491563549461072725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677202327709032974048483 8515803491563549461072725)
            ·
              refine ⟨49897286083380172623473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8515803491563549461072725 49897286083380172623473)
              ·
                rfl

theorem cell20_983893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 9].length) (baseStart_983893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983893 prefixEnd_983893 := by exact prefixLift 983893
  have htrace : WordTrace (prefixWord ++ tailWord_983893) baseStart_983893 baseEnd_983893 := by
    simpa [prefixWord, tailWord_983893, baseEnd_983893] using wordTrace_append hprefix tailTrace_983893
  have hstable : (prefixWord ++ tailWord_983893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983893).length < 2 ^ (prefixWord ++ tailWord_983893).sum := by decide
  have hdescent : baseEnd_983893 < baseStart_983893 := by decide
  rcases family_descends (prefixWord ++ tailWord_983893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983903 : List Nat := [1, 1, 2, 3, 1, 3, 1, 6, 2]
def baseStart_983903 : Nat := 118140960795 + 983903 * 2 ^ 59
def prefixEnd_983903 : Nat := 4983230072969 + 3 ^ 40 * 983903 * 2
def baseEnd_983903 : Nat := 449080139022905963277883

theorem tailTrace_983903 : CollatzResearch.WordTrace tailWord_983903 prefixEnd_983903 449080139022905963277883 := by
  unfold tailWord_983903
  simp only [CollatzResearch.WordTrace]
  refine ⟨35885890554494943099380363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23923927036329962066253575 35885890554494943099380363)
  ·
    refine ⟨53828835831742414649070545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35885890554494943099380363 53828835831742414649070545)
    ·
      refine ⟨40371626873806810986802909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53828835831742414649070545 40371626873806810986802909)
      ·
        refine ⟨15139360077677554120051091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40371626873806810986802909 15139360077677554120051091)
        ·
          refine ⟨22709040116516331180076637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15139360077677554120051091 22709040116516331180076637)
          ·
            refine ⟨8515890043693624192528739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22709040116516331180076637 8515890043693624192528739)
            ·
              refine ⟨12773835065540436288793109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8515890043693624192528739 12773835065540436288793109)
              ·
                refine ⟨598773518697207951037177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12773835065540436288793109 598773518697207951037177)
                ·
                  refine ⟨449080139022905963277883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598773518697207951037177 449080139022905963277883)
                  ·
                    rfl

theorem cell20_983903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 2].length) (baseStart_983903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983903 prefixEnd_983903 := by exact prefixLift 983903
  have htrace : WordTrace (prefixWord ++ tailWord_983903) baseStart_983903 baseEnd_983903 := by
    simpa [prefixWord, tailWord_983903, baseEnd_983903] using wordTrace_append hprefix tailTrace_983903
  have hstable : (prefixWord ++ tailWord_983903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983903).length < 2 ^ (prefixWord ++ tailWord_983903).sum := by decide
  have hdescent : baseEnd_983903 < baseStart_983903 := by decide
  rcases family_descends (prefixWord ++ tailWord_983903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983954 : List Nat := [3, 2, 3, 2, 2, 1, 3, 2, 2]
def baseStart_983954 : Nat := 118140960795 + 983954 * 2 ^ 59
def prefixEnd_983954 : Nat := 4983230072969 + 3 ^ 40 * 983954 * 2
def baseEnd_983954 : Nat := 449103416812576452577675

theorem tailTrace_983954 : CollatzResearch.WordTrace tailWord_983954 prefixEnd_983954 449103416812576452577675 := by
  unfold tailWord_983954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971937669327544702371729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23925167118206785872991277 8971937669327544702371729)
  ·
    refine ⟨6728953251995658526778797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8971937669327544702371729 6728953251995658526778797)
    ·
      refine ⟨2523357469498371947542049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6728953251995658526778797 2523357469498371947542049)
      ·
        refine ⟨1892518102123778960656537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2523357469498371947542049 1892518102123778960656537)
        ·
          refine ⟨1419388576592834220492403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1892518102123778960656537 1419388576592834220492403)
          ·
            refine ⟨2129082864889251330738605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419388576592834220492403 2129082864889251330738605)
            ·
              refine ⟨798406074333469249026977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2129082864889251330738605 798406074333469249026977)
              ·
                refine ⟨598804555750101936770233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798406074333469249026977 598804555750101936770233)
                ·
                  refine ⟨449103416812576452577675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598804555750101936770233 449103416812576452577675)
                  ·
                    rfl

theorem cell20_983954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_983954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_983954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_983954 prefixEnd_983954 := by exact prefixLift 983954
  have htrace : WordTrace (prefixWord ++ tailWord_983954) baseStart_983954 baseEnd_983954 := by
    simpa [prefixWord, tailWord_983954, baseEnd_983954] using wordTrace_append hprefix tailTrace_983954
  have hstable : (prefixWord ++ tailWord_983954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983954).length < 2 ^ (prefixWord ++ tailWord_983954).sum := by decide
  have hdescent : baseEnd_983954 < baseStart_983954 := by decide
  rcases family_descends (prefixWord ++ tailWord_983954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984017 : List Nat := [1, 2, 2, 1, 2, 1, 5, 4, 2]
def baseStart_984017 : Nat := 118140960795 + 984017 * 2 ^ 59
def prefixEnd_984017 : Nat := 4983230072969 + 3 ^ 40 * 984017 * 2
def baseEnd_984017 : Nat := 449132171729228233477417

theorem tailTrace_984017 : CollatzResearch.WordTrace tailWord_984017 prefixEnd_984017 449132171729228233477417 := by
  unfold tailWord_984017
  simp only [CollatzResearch.WordTrace]
  refine ⟨35890048476081940569030305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23926698984054627046020203 35890048476081940569030305)
  ·
    refine ⟨26917536357061455426772729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35890048476081940569030305 26917536357061455426772729)
    ·
      refine ⟨20188152267796091570079547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26917536357061455426772729 20188152267796091570079547)
      ·
        refine ⟨30282228401694137355119321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20188152267796091570079547 30282228401694137355119321)
        ·
          refine ⟨22711671301270603016339491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30282228401694137355119321 22711671301270603016339491)
          ·
            refine ⟨34067506951905904524509237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22711671301270603016339491 34067506951905904524509237)
            ·
              refine ⟨3193828776741178549172741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34067506951905904524509237 3193828776741178549172741)
              ·
                refine ⟨598842895638970977969889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3193828776741178549172741 598842895638970977969889)
                ·
                  refine ⟨449132171729228233477417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598842895638970977969889 449132171729228233477417)
                  ·
                    rfl

theorem cell20_984017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_984017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984017 prefixEnd_984017 := by exact prefixLift 984017
  have htrace : WordTrace (prefixWord ++ tailWord_984017) baseStart_984017 baseEnd_984017 := by
    simpa [prefixWord, tailWord_984017, baseEnd_984017] using wordTrace_append hprefix tailTrace_984017
  have hstable : (prefixWord ++ tailWord_984017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984017).length < 2 ^ (prefixWord ++ tailWord_984017).sum := by decide
  have hdescent : baseEnd_984017 < baseStart_984017 := by decide
  rcases family_descends (prefixWord ++ tailWord_984017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984024 : List Nat := [2, 1, 2, 2, 2, 5, 1, 5]
def baseStart_984024 : Nat := 118140960795 + 984024 * 2 ^ 59
def prefixEnd_984024 : Nat := 4983230072969 + 3 ^ 40 * 984024 * 2
def baseEnd_984024 : Nat := 149711788906655773414685

theorem tailTrace_984024 : CollatzResearch.WordTrace tailWord_984024 prefixEnd_984024 149711788906655773414685 := by
  unfold tailWord_984024
  simp only [CollatzResearch.WordTrace]
  refine ⟨17945151893528290382267563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23926869191371053843023417 17945151893528290382267563)
  ·
    refine ⟨26917727840292435573401345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17945151893528290382267563 26917727840292435573401345)
    ·
      refine ⟨20188295880219326680051009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26917727840292435573401345 20188295880219326680051009)
      ·
        refine ⟨15141221910164495010038257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20188295880219326680051009 15141221910164495010038257)
        ·
          refine ⟨11355916432623371257528693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15141221910164495010038257 11355916432623371257528693)
          ·
            refine ⟨1064617165558441055393315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11355916432623371257528693 1064617165558441055393315)
            ·
              refine ⟨1596925748337661583089973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064617165558441055393315 1596925748337661583089973)
              ·
                refine ⟨149711788906655773414685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1596925748337661583089973 149711788906655773414685)
                ·
                  rfl

theorem cell20_984024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_984024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984024 prefixEnd_984024 := by exact prefixLift 984024
  have htrace : WordTrace (prefixWord ++ tailWord_984024) baseStart_984024 baseEnd_984024 := by
    simpa [prefixWord, tailWord_984024, baseEnd_984024] using wordTrace_append hprefix tailTrace_984024
  have hstable : (prefixWord ++ tailWord_984024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984024).length < 2 ^ (prefixWord ++ tailWord_984024).sum := by decide
  have hdescent : baseEnd_984024 < baseStart_984024 := by decide
  rcases family_descends (prefixWord ++ tailWord_984024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984034 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_984034 : Nat := 118140960795 + 984034 * 2 ^ 59
def prefixEnd_984034 : Nat := 4983230072969 + 3 ^ 40 * 984034 * 2
def baseEnd_984034 : Nat := 449139930992451729910681

theorem tailTrace_984034 : CollatzResearch.WordTrace tailWord_984034 prefixEnd_984034 449139930992451729910681 := by
  unfold tailWord_984034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8972667129255088118099789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23927112344680234981599437 8972667129255088118099789)
  ·
    refine ⟨3364750173470658044287421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8972667129255088118099789 3364750173470658044287421)
    ·
      refine ⟨1261781315051496766607783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3364750173470658044287421 1261781315051496766607783)
      ·
        refine ⟨1892671972577245149911675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1261781315051496766607783 1892671972577245149911675)
        ·
          refine ⟨2839007958865867724867513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892671972577245149911675 2839007958865867724867513)
          ·
            refine ⟨2129255969149400793650635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2839007958865867724867513 2129255969149400793650635)
            ·
              refine ⟨3193883953724101190475953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129255969149400793650635 3193883953724101190475953)
              ·
                refine ⟨2395412965293075892856965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3193883953724101190475953 2395412965293075892856965)
                ·
                  refine ⟨449139930992451729910681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2395412965293075892856965 449139930992451729910681)
                  ·
                    rfl

theorem cell20_984034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_984034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984034 prefixEnd_984034 := by exact prefixLift 984034
  have htrace : WordTrace (prefixWord ++ tailWord_984034) baseStart_984034 baseEnd_984034 := by
    simpa [prefixWord, tailWord_984034, baseEnd_984034] using wordTrace_append hprefix tailTrace_984034
  have hstable : (prefixWord ++ tailWord_984034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984034).length < 2 ^ (prefixWord ++ tailWord_984034).sum := by decide
  have hdescent : baseEnd_984034 < baseStart_984034 := by decide
  rcases family_descends (prefixWord ++ tailWord_984034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984059 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_984059 : Nat := 118140960795 + 984059 * 2 ^ 59
def prefixEnd_984059 : Nat := 4983230072969 + 3 ^ 40 * 984059 * 2
def baseEnd_984059 : Nat := 449151341673662754077245

theorem tailTrace_984059 : CollatzResearch.WordTrace tailWord_984059 prefixEnd_984059 449151341673662754077245 := by
  unfold tailWord_984059
  simp only [CollatzResearch.WordTrace]
  refine ⟨35891580341929781742059231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23927720227953187828039487 35891580341929781742059231)
  ·
    refine ⟨53837370512894672613088847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35891580341929781742059231 53837370512894672613088847)
    ·
      refine ⟨80756055769342008919633271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53837370512894672613088847 80756055769342008919633271)
      ·
        refine ⟨121134083654013013379449907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80756055769342008919633271 121134083654013013379449907)
        ·
          refine ⟨181701125481019520069174861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121134083654013013379449907 181701125481019520069174861)
          ·
            refine ⟨68137922055382320025940573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181701125481019520069174861 68137922055382320025940573)
            ·
              refine ⟨25551720770768370009727715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68137922055382320025940573 25551720770768370009727715)
              ·
                refine ⟨38327581156152555014591573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25551720770768370009727715 38327581156152555014591573)
                ·
                  refine ⟨449151341673662754077245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38327581156152555014591573 449151341673662754077245)
                  ·
                    rfl

theorem cell20_984059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_984059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984059 prefixEnd_984059 := by exact prefixLift 984059
  have htrace : WordTrace (prefixWord ++ tailWord_984059) baseStart_984059 baseEnd_984059 := by
    simpa [prefixWord, tailWord_984059, baseEnd_984059] using wordTrace_append hprefix tailTrace_984059
  have hstable : (prefixWord ++ tailWord_984059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984059).length < 2 ^ (prefixWord ++ tailWord_984059).sum := by decide
  have hdescent : baseEnd_984059 < baseStart_984059 := by decide
  rcases family_descends (prefixWord ++ tailWord_984059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984076 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_984076 : Nat := 118140960795 + 984076 * 2 ^ 59
def prefixEnd_984076 : Nat := 4983230072969 + 3 ^ 40 * 984076 * 2
def baseEnd_984076 : Nat := 449159100936886250510509

theorem tailTrace_984076 : CollatzResearch.WordTrace tailWord_984076 prefixEnd_984076 449159100936886250510509 := by
  unfold tailWord_984076
  simp only [CollatzResearch.WordTrace]
  refine ⟨17946100191434096822714041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23928133588578795763618721 17946100191434096822714041)
  ·
    refine ⟨13459575143575572617035531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17946100191434096822714041 13459575143575572617035531)
    ·
      refine ⟨20189362715363358925553297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13459575143575572617035531 20189362715363358925553297)
      ·
        refine ⟨15142022036522519194164973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20189362715363358925553297 15142022036522519194164973)
        ·
          refine ⟨5678258263695944697811865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15142022036522519194164973 5678258263695944697811865)
          ·
            refine ⟨4258693697771958523358899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5678258263695944697811865 4258693697771958523358899)
            ·
              refine ⟨6388040546657937785038349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258693697771958523358899 6388040546657937785038349)
              ·
                refine ⟨2395515204996726669389381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6388040546657937785038349 2395515204996726669389381)
                ·
                  refine ⟨449159100936886250510509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2395515204996726669389381 449159100936886250510509)
                  ·
                    rfl

theorem cell20_984076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_984076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984076 prefixEnd_984076 := by exact prefixLift 984076
  have htrace : WordTrace (prefixWord ++ tailWord_984076) baseStart_984076 baseEnd_984076 := by
    simpa [prefixWord, tailWord_984076, baseEnd_984076] using wordTrace_append hprefix tailTrace_984076
  have hstable : (prefixWord ++ tailWord_984076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984076).length < 2 ^ (prefixWord ++ tailWord_984076).sum := by decide
  have hdescent : baseEnd_984076 < baseStart_984076 := by decide
  rcases family_descends (prefixWord ++ tailWord_984076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984096 : List Nat := [2, 1, 1, 7, 1, 2, 2, 4]
def baseStart_984096 : Nat := 118140960795 + 984096 * 2 ^ 59
def prefixEnd_984096 : Nat := 4983230072969 + 3 ^ 40 * 984096 * 2
def baseEnd_984096 : Nat := 149722743160618356614587

theorem tailTrace_984096 : CollatzResearch.WordTrace tailWord_984096 prefixEnd_984096 149722743160618356614587 := by
  unfold tailWord_984096
  simp only [CollatzResearch.WordTrace]
  refine ⟨17946464921397868530578071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23928619895197158040770761 17946464921397868530578071)
  ·
    refine ⟨26919697382096802795867107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17946464921397868530578071 26919697382096802795867107)
    ·
      refine ⟨40379546073145204193800661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26919697382096802795867107 40379546073145204193800661)
      ·
        refine ⟨946395611089340723292203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 40379546073145204193800661 946395611089340723292203)
        ·
          refine ⟨1419593416634011084938305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946395611089340723292203 1419593416634011084938305)
          ·
            refine ⟨1064695062475508313703729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1419593416634011084938305 1064695062475508313703729)
            ·
              refine ⟨798521296856631235277797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064695062475508313703729 798521296856631235277797)
              ·
                refine ⟨149722743160618356614587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 798521296856631235277797 149722743160618356614587)
                ·
                  rfl

theorem cell20_984096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_984096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984096 prefixEnd_984096 := by exact prefixLift 984096
  have htrace : WordTrace (prefixWord ++ tailWord_984096) baseStart_984096 baseEnd_984096 := by
    simpa [prefixWord, tailWord_984096, baseEnd_984096] using wordTrace_append hprefix tailTrace_984096
  have hstable : (prefixWord ++ tailWord_984096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984096).length < 2 ^ (prefixWord ++ tailWord_984096).sum := by decide
  have hdescent : baseEnd_984096 < baseStart_984096 := by decide
  rcases family_descends (prefixWord ++ tailWord_984096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984100 : List Nat := [2, 3, 1, 4, 1, 2, 1, 6]
def baseStart_984100 : Nat := 118140960795 + 984100 * 2 ^ 59
def prefixEnd_984100 : Nat := 4983230072969 + 3 ^ 40 * 984100 * 2
def baseEnd_984100 : Nat := 149723351730282944570137

theorem tailTrace_984100 : CollatzResearch.WordTrace tailWord_984100 prefixEnd_984100 149723351730282944570137 := by
  unfold tailWord_984100
  simp only [CollatzResearch.WordTrace]
  refine ⟨17946537867390622872150877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23928717156520830496201169 17946537867390622872150877)
  ·
    refine ⟨6729951700271483577056579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17946537867390622872150877 6729951700271483577056579)
    ·
      refine ⟨10094927550407225365584869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6729951700271483577056579 10094927550407225365584869)
      ·
        refine ⟨1892798915701354756047163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10094927550407225365584869 1892798915701354756047163)
        ·
          refine ⟨2839198373552032134070745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892798915701354756047163 2839198373552032134070745)
          ·
            refine ⟨2129398780164024100553059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2839198373552032134070745 2129398780164024100553059)
            ·
              refine ⟨3194098170246036150829589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129398780164024100553059 3194098170246036150829589)
              ·
                refine ⟨149723351730282944570137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3194098170246036150829589 149723351730282944570137)
                ·
                  rfl

theorem cell20_984100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_984100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984100 prefixEnd_984100 := by exact prefixLift 984100
  have htrace : WordTrace (prefixWord ++ tailWord_984100) baseStart_984100 baseEnd_984100 := by
    simpa [prefixWord, tailWord_984100, baseEnd_984100] using wordTrace_append hprefix tailTrace_984100
  have hstable : (prefixWord ++ tailWord_984100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984100).length < 2 ^ (prefixWord ++ tailWord_984100).sum := by decide
  have hdescent : baseEnd_984100 < baseStart_984100 := by decide
  rcases family_descends (prefixWord ++ tailWord_984100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984106 : List Nat := [3, 1, 4, 1, 4, 1, 1, 3, 2]
def baseStart_984106 : Nat := 118140960795 + 984106 * 2 ^ 59
def prefixEnd_984106 : Nat := 4983230072969 + 3 ^ 40 * 984106 * 2
def baseEnd_984106 : Nat := 449172793754339479510387

theorem tailTrace_984106 : CollatzResearch.WordTrace tailWord_984106 prefixEnd_984106 449172793754339479510387 := by
  unfold tailWord_984106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973323643189877192255043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23928863048506339179346781 8973323643189877192255043)
  ·
    refine ⟨13459985464784815788382565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8973323643189877192255043 13459985464784815788382565)
    ·
      refine ⟨2523747274647152960321731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13459985464784815788382565 2523747274647152960321731)
      ·
        refine ⟨3785620911970729440482597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523747274647152960321731 3785620911970729440482597)
        ·
          refine ⟨709803920994511770090487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3785620911970729440482597 709803920994511770090487)
          ·
            refine ⟨1064705881491767655135731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709803920994511770090487 1064705881491767655135731)
            ·
              refine ⟨1597058822237651482703597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064705881491767655135731 1597058822237651482703597)
              ·
                refine ⟨598897058339119306013849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597058822237651482703597 598897058339119306013849)
                ·
                  refine ⟨449172793754339479510387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598897058339119306013849 449172793754339479510387)
                  ·
                    rfl

theorem cell20_984106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_984106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984106 prefixEnd_984106 := by exact prefixLift 984106
  have htrace : WordTrace (prefixWord ++ tailWord_984106) baseStart_984106 baseEnd_984106 := by
    simpa [prefixWord, tailWord_984106, baseEnd_984106] using wordTrace_append hprefix tailTrace_984106
  have hstable : (prefixWord ++ tailWord_984106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984106).length < 2 ^ (prefixWord ++ tailWord_984106).sum := by decide
  have hdescent : baseEnd_984106 < baseStart_984106 := by decide
  rcases family_descends (prefixWord ++ tailWord_984106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984121 : List Nat := [1, 2, 1, 5, 2, 1, 8]
def baseStart_984121 : Nat := 118140960795 + 984121 * 2 ^ 59
def prefixEnd_984121 : Nat := 4983230072969 + 3 ^ 40 * 984121 * 2
def baseEnd_984121 : Nat := 49908848907007343778925

theorem tailTrace_984121 : CollatzResearch.WordTrace tailWord_984121 prefixEnd_984121 49908848907007343778925 := by
  unfold tailWord_984121
  simp only [CollatzResearch.WordTrace]
  refine ⟨35893841667705166330816217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23929227778470110887210811 35893841667705166330816217)
  ·
    refine ⟨26920381250778874748112163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35893841667705166330816217 26920381250778874748112163)
    ·
      refine ⟨40380571876168312122168245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26920381250778874748112163 40380571876168312122168245)
      ·
        refine ⟨3785678613390779261453273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40380571876168312122168245 3785678613390779261453273)
        ·
          refine ⟨2839258960043084446089955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3785678613390779261453273 2839258960043084446089955)
          ·
            refine ⟨4258888440064626669134933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839258960043084446089955 4258888440064626669134933)
            ·
              refine ⟨49908848907007343778925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4258888440064626669134933 49908848907007343778925)
              ·
                rfl

theorem cell20_984121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 8].length) (baseStart_984121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984121 prefixEnd_984121 := by exact prefixLift 984121
  have htrace : WordTrace (prefixWord ++ tailWord_984121) baseStart_984121 baseEnd_984121 := by
    simpa [prefixWord, tailWord_984121, baseEnd_984121] using wordTrace_append hprefix tailTrace_984121
  have hstable : (prefixWord ++ tailWord_984121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984121).length < 2 ^ (prefixWord ++ tailWord_984121).sum := by decide
  have hdescent : baseEnd_984121 < baseStart_984121 := by decide
  rcases family_descends (prefixWord ++ tailWord_984121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984128 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_984128 : Nat := 118140960795 + 984128 * 2 ^ 59
def prefixEnd_984128 : Nat := 4983230072969 + 3 ^ 40 * 984128 * 2
def baseEnd_984128 : Nat := 449182835153805180776963

theorem tailTrace_984128 : CollatzResearch.WordTrace tailWord_984128 prefixEnd_984128 449182835153805180776963 := by
  unfold tailWord_984128
  simp only [CollatzResearch.WordTrace]
  refine ⟨17947048489339903263160519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23929397985786537684214025 17947048489339903263160519)
  ·
    refine ⟨26920572734009854894740779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17947048489339903263160519 26920572734009854894740779)
    ·
      refine ⟨40380859101014782342111169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26920572734009854894740779 40380859101014782342111169)
      ·
        refine ⟨30285644325761086756583377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40380859101014782342111169 30285644325761086756583377)
        ·
          refine ⟨22714233244320815067437533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30285644325761086756583377 22714233244320815067437533)
          ·
            refine ⟨8517837466620305650289075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22714233244320815067437533 8517837466620305650289075)
            ·
              refine ⟨12776756199930458475433613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8517837466620305650289075 12776756199930458475433613)
              ·
                refine ⟨4791283574973921928287605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12776756199930458475433613 4791283574973921928287605)
                ·
                  refine ⟨449182835153805180776963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4791283574973921928287605 449182835153805180776963)
                  ·
                    rfl

theorem cell20_984128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_984128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984128 prefixEnd_984128 := by exact prefixLift 984128
  have htrace : WordTrace (prefixWord ++ tailWord_984128) baseStart_984128 baseEnd_984128 := by
    simpa [prefixWord, tailWord_984128, baseEnd_984128] using wordTrace_append hprefix tailTrace_984128
  have hstable : (prefixWord ++ tailWord_984128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984128).length < 2 ^ (prefixWord ++ tailWord_984128).sum := by decide
  have hdescent : baseEnd_984128 < baseStart_984128 := by decide
  rcases family_descends (prefixWord ++ tailWord_984128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984141 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 3]
def baseStart_984141 : Nat := 118140960795 + 984141 * 2 ^ 59
def prefixEnd_984141 : Nat := 4983230072969 + 3 ^ 40 * 984141 * 2
def baseEnd_984141 : Nat := 449188768708034913343577

theorem tailTrace_984141 : CollatzResearch.WordTrace tailWord_984141 prefixEnd_984141 449188768708034913343577 := by
  unfold tailWord_984141
  simp only [CollatzResearch.WordTrace]
  refine ⟨35894571127632709746544277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23929714085088473164362851 35894571127632709746544277)
  ·
    refine ⟨1682558021607783269369263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35894571127632709746544277 1682558021607783269369263)
    ·
      refine ⟨2523837032411674904053895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1682558021607783269369263 2523837032411674904053895)
      ·
        refine ⟨3785755548617512356080843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523837032411674904053895 3785755548617512356080843)
        ·
          refine ⟨5678633322926268534121265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3785755548617512356080843 5678633322926268534121265)
          ·
            refine ⟨4258974992194701400590949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5678633322926268534121265 4258974992194701400590949)
            ·
              refine ⟨798557811036506512610803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4258974992194701400590949 798557811036506512610803)
              ·
                refine ⟨1197836716554759768916205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798557811036506512610803 1197836716554759768916205)
                ·
                  refine ⟨449188768708034913343577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197836716554759768916205 449188768708034913343577)
                  ·
                    rfl

theorem cell20_984141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_984141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984141 prefixEnd_984141 := by exact prefixLift 984141
  have htrace : WordTrace (prefixWord ++ tailWord_984141) baseStart_984141 baseEnd_984141 := by
    simpa [prefixWord, tailWord_984141, baseEnd_984141] using wordTrace_append hprefix tailTrace_984141
  have hstable : (prefixWord ++ tailWord_984141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984141).length < 2 ^ (prefixWord ++ tailWord_984141).sum := by decide
  have hdescent : baseEnd_984141 < baseStart_984141 := by decide
  rcases family_descends (prefixWord ++ tailWord_984141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984183 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 3]
def baseStart_984183 : Nat := 118140960795 + 984183 * 2 ^ 59
def prefixEnd_984183 : Nat := 4983230072969 + 3 ^ 40 * 984183 * 2
def baseEnd_984183 : Nat := 449207938652469433943405

theorem tailTrace_984183 : CollatzResearch.WordTrace tailWord_984183 prefixEnd_984183 449207938652469433943405 := by
  unfold tailWord_984183
  simp only [CollatzResearch.WordTrace]
  refine ⟨35896102993480550919573203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23930735328987033946382135 35896102993480550919573203)
  ·
    refine ⟨53844154490220826379359805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35896102993480550919573203 53844154490220826379359805)
    ·
      refine ⟨20191557933832809892259927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53844154490220826379359805 20191557933832809892259927)
      ·
        refine ⟨30287336900749214838389891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20191557933832809892259927 30287336900749214838389891)
        ·
          refine ⟨45431005351123822257584837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30287336900749214838389891 45431005351123822257584837)
          ·
            refine ⟨8518313503335716673297157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45431005351123822257584837 8518313503335716673297157)
            ·
              refine ⟨1597183781875446876243217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8518313503335716673297157 1597183781875446876243217)
              ·
                refine ⟨1197887836406585157182413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597183781875446876243217 1197887836406585157182413)
                ·
                  refine ⟨449207938652469433943405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197887836406585157182413 449207938652469433943405)
                  ·
                    rfl

theorem cell20_984183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 3].length) (baseStart_984183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984183 prefixEnd_984183 := by exact prefixLift 984183
  have htrace : WordTrace (prefixWord ++ tailWord_984183) baseStart_984183 baseEnd_984183 := by
    simpa [prefixWord, tailWord_984183, baseEnd_984183] using wordTrace_append hprefix tailTrace_984183
  have hstable : (prefixWord ++ tailWord_984183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984183).length < 2 ^ (prefixWord ++ tailWord_984183).sum := by decide
  have hdescent : baseEnd_984183 < baseStart_984183 := by decide
  rcases family_descends (prefixWord ++ tailWord_984183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984211 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_984211 : Nat := 118140960795 + 984211 * 2 ^ 59
def prefixEnd_984211 : Nat := 4983230072969 + 3 ^ 40 * 984211 * 2
def baseEnd_984211 : Nat := 449220718615425781009957

theorem tailTrace_984211 : CollatzResearch.WordTrace tailWord_984211 prefixEnd_984211 449220718615425781009957 := by
  unfold tailWord_984211
  simp only [CollatzResearch.WordTrace]
  refine ⟨35897124237379111701592487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23931416158252741134394991 35897124237379111701592487)
  ·
    refine ⟨53845686356068667552388731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35897124237379111701592487 53845686356068667552388731)
    ·
      refine ⟨80768529534103001328583097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53845686356068667552388731 80768529534103001328583097)
      ·
        refine ⟨60576397150577250996437323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80768529534103001328583097 60576397150577250996437323)
        ·
          refine ⟨90864595725865876494655985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60576397150577250996437323 90864595725865876494655985)
          ·
            refine ⟨68148446794399407370991989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90864595725865876494655985 68148446794399407370991989)
            ·
              refine ⟨6388916886974944441030499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68148446794399407370991989 6388916886974944441030499)
              ·
                refine ⟨9583375330462416661545749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388916886974944441030499 9583375330462416661545749)
                ·
                  refine ⟨449220718615425781009957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9583375330462416661545749 449220718615425781009957)
                  ·
                    rfl

theorem cell20_984211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_984211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984211 prefixEnd_984211 := by exact prefixLift 984211
  have htrace : WordTrace (prefixWord ++ tailWord_984211) baseStart_984211 baseEnd_984211 := by
    simpa [prefixWord, tailWord_984211, baseEnd_984211] using wordTrace_append hprefix tailTrace_984211
  have hstable : (prefixWord ++ tailWord_984211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984211).length < 2 ^ (prefixWord ++ tailWord_984211).sum := by decide
  have hdescent : baseEnd_984211 < baseStart_984211 := by decide
  rcases family_descends (prefixWord ++ tailWord_984211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984266 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_984266 : Nat := 118140960795 + 984266 * 2 ^ 59
def prefixEnd_984266 : Nat := 4983230072969 + 3 ^ 40 * 984266 * 2
def baseEnd_984266 : Nat := 449245822114090034176399

theorem tailTrace_984266 : CollatzResearch.WordTrace tailWord_984266 prefixEnd_984266 449245822114090034176399 := by
  unfold tailWord_984266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8974782563044964023711163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23932753501453237396563101 8974782563044964023711163)
  ·
    refine ⟨13462173844567446035566745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8974782563044964023711163 13462173844567446035566745)
    ·
      refine ⟨10096630383425584526675059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13462173844567446035566745 10096630383425584526675059)
      ·
        refine ⟨15144945575138376790012589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10096630383425584526675059 15144945575138376790012589)
        ·
          refine ⟨5679354590676891296254721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15144945575138376790012589 5679354590676891296254721)
          ·
            refine ⟨4259515943007668472191041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5679354590676891296254721 4259515943007668472191041)
            ·
              refine ⟨3194636957255751354143281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259515943007668472191041 3194636957255751354143281)
              ·
                refine ⟨2395977717941813515607461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3194636957255751354143281 2395977717941813515607461)
                ·
                  refine ⟨449245822114090034176399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2395977717941813515607461 449245822114090034176399)
                  ·
                    rfl

theorem cell20_984266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_984266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984266 prefixEnd_984266 := by exact prefixLift 984266
  have htrace : WordTrace (prefixWord ++ tailWord_984266) baseStart_984266 baseEnd_984266 := by
    simpa [prefixWord, tailWord_984266, baseEnd_984266] using wordTrace_append hprefix tailTrace_984266
  have hstable : (prefixWord ++ tailWord_984266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984266).length < 2 ^ (prefixWord ++ tailWord_984266).sum := by decide
  have hdescent : baseEnd_984266 < baseStart_984266 := by decide
  rcases family_descends (prefixWord ++ tailWord_984266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984287 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_984287 : Nat := 118140960795 + 984287 * 2 ^ 59
def prefixEnd_984287 : Nat := 4983230072969 + 3 ^ 40 * 984287 * 2
def baseEnd_984287 : Nat := 449255407086307294476313

theorem tailTrace_984287 : CollatzResearch.WordTrace tailWord_984287 prefixEnd_984287 449255407086307294476313 := by
  unfold tailWord_984287
  simp only [CollatzResearch.WordTrace]
  refine ⟨35899896185103776681359115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23933264123402517787572743 35899896185103776681359115)
  ·
    refine ⟨53849844277655665022038673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35899896185103776681359115 53849844277655665022038673)
    ·
      refine ⟨40387383208241748766529005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53849844277655665022038673 40387383208241748766529005)
      ·
        refine ⟨15145268703090655787448377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40387383208241748766529005 15145268703090655787448377)
        ·
          refine ⟨11358951527317991840586283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15145268703090655787448377 11358951527317991840586283)
          ·
            refine ⟨17038427290976987760879425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11358951527317991840586283 17038427290976987760879425)
            ·
              refine ⟨12778820468232740820659569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17038427290976987760879425 12778820468232740820659569)
              ·
                refine ⟨9584115351174555615494677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12778820468232740820659569 9584115351174555615494677)
                ·
                  refine ⟨449255407086307294476313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9584115351174555615494677 449255407086307294476313)
                  ·
                    rfl

theorem cell20_984287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_984287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984287 prefixEnd_984287 := by exact prefixLift 984287
  have htrace : WordTrace (prefixWord ++ tailWord_984287) baseStart_984287 baseEnd_984287 := by
    simpa [prefixWord, tailWord_984287, baseEnd_984287] using wordTrace_append hprefix tailTrace_984287
  have hstable : (prefixWord ++ tailWord_984287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984287).length < 2 ^ (prefixWord ++ tailWord_984287).sum := by decide
  have hdescent : baseEnd_984287 < baseStart_984287 := by decide
  rcases family_descends (prefixWord ++ tailWord_984287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984300 : List Nat := [2, 2, 1, 1, 2, 5, 3, 2, 2]
def baseStart_984300 : Nat := 118140960795 + 984300 * 2 ^ 59
def prefixEnd_984300 : Nat := 4983230072969 + 3 ^ 40 * 984300 * 2
def baseEnd_984300 : Nat := 449261340640537027042927

theorem tailTrace_984300 : CollatzResearch.WordTrace tailWord_984300 prefixEnd_984300 449261340640537027042927 := by
  unfold tailWord_984300
  simp only [CollatzResearch.WordTrace]
  refine ⟨17950185167028339950791177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23933580222704453267721569 17950185167028339950791177)
  ·
    refine ⟨13462638875271254963093383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17950185167028339950791177 13462638875271254963093383)
    ·
      refine ⟨20193958312906882444640075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13462638875271254963093383 20193958312906882444640075)
      ·
        refine ⟨30290937469360323666960113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20193958312906882444640075 30290937469360323666960113)
        ·
          refine ⟨22718203102020242750220085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30290937469360323666960113 22718203102020242750220085)
          ·
            refine ⟨2129831540814397757833133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22718203102020242750220085 2129831540814397757833133)
            ·
              refine ⟨798686827805399159187425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2129831540814397757833133 798686827805399159187425)
              ·
                refine ⟨599015120854049369390569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798686827805399159187425 599015120854049369390569)
                ·
                  refine ⟨449261340640537027042927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599015120854049369390569 449261340640537027042927)
                  ·
                    rfl

theorem cell20_984300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_984300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984300 prefixEnd_984300 := by exact prefixLift 984300
  have htrace : WordTrace (prefixWord ++ tailWord_984300) baseStart_984300 baseEnd_984300 := by
    simpa [prefixWord, tailWord_984300, baseEnd_984300] using wordTrace_append hprefix tailTrace_984300
  have hstable : (prefixWord ++ tailWord_984300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984300).length < 2 ^ (prefixWord ++ tailWord_984300).sum := by decide
  have hdescent : baseEnd_984300 < baseStart_984300 := by decide
  rcases family_descends (prefixWord ++ tailWord_984300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984325 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_984325 : Nat := 118140960795 + 984325 * 2 ^ 59
def prefixEnd_984325 : Nat := 4983230072969 + 3 ^ 40 * 984325 * 2
def baseEnd_984325 : Nat := 449272751321748051209491

theorem tailTrace_984325 : CollatzResearch.WordTrace tailWord_984325 prefixEnd_984325 449272751321748051209491 := by
  unfold tailWord_984325
  simp only [CollatzResearch.WordTrace]
  refine ⟨35901282158966109171242429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23934188105977406114161619 35901282158966109171242429)
  ·
    refine ⟨13462980809612290939215911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35901282158966109171242429 13462980809612290939215911)
    ·
      refine ⟨20194471214418436408823867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13462980809612290939215911 20194471214418436408823867)
      ·
        refine ⟨30291706821627654613235801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20194471214418436408823867 30291706821627654613235801)
        ·
          refine ⟨22718780116220740959926851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30291706821627654613235801 22718780116220740959926851)
          ·
            refine ⟨34078170174331111439890277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22718780116220740959926851 34078170174331111439890277)
            ·
              refine ⟨6389656907687083394979427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34078170174331111439890277 6389656907687083394979427)
              ·
                refine ⟨9584485361530625092469141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389656907687083394979427 9584485361530625092469141)
                ·
                  refine ⟨449272751321748051209491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9584485361530625092469141 449272751321748051209491)
                  ·
                    rfl

theorem cell20_984325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_984325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984325 prefixEnd_984325 := by exact prefixLift 984325
  have htrace : WordTrace (prefixWord ++ tailWord_984325) baseStart_984325 baseEnd_984325 := by
    simpa [prefixWord, tailWord_984325, baseEnd_984325] using wordTrace_append hprefix tailTrace_984325
  have hstable : (prefixWord ++ tailWord_984325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984325).length < 2 ^ (prefixWord ++ tailWord_984325).sum := by decide
  have hdescent : baseEnd_984325 < baseStart_984325 := by decide
  rcases family_descends (prefixWord ++ tailWord_984325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984349 : List Nat := [1, 4, 2, 3, 1, 9]
def baseStart_984349 : Nat := 118140960795 + 984349 * 2 ^ 59
def prefixEnd_984349 : Nat := 4983230072969 + 3 ^ 40 * 984349 * 2
def baseEnd_984349 : Nat := 16640137243544838311459

theorem tailTrace_984349 : CollatzResearch.WordTrace tailWord_984349 prefixEnd_984349 16640137243544838311459 := by
  unfold tailWord_984349
  simp only [CollatzResearch.WordTrace]
  refine ⟨35902157510879161270116101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23934771673919440846744067 35902157510879161270116101)
  ·
    refine ⟨6731654533289842738146769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35902157510879161270116101 6731654533289842738146769)
    ·
      refine ⟨5048740899967382053610077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6731654533289842738146769 5048740899967382053610077)
      ·
        refine ⟨1893277837487768270103779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5048740899967382053610077 1893277837487768270103779)
        ·
          refine ⟨2839916756231652405155669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893277837487768270103779 2839916756231652405155669)
          ·
            refine ⟨16640137243544838311459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2839916756231652405155669 16640137243544838311459)
            ·
              rfl

theorem cell20_984349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 9].length) (baseStart_984349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984349 prefixEnd_984349 := by exact prefixLift 984349
  have htrace : WordTrace (prefixWord ++ tailWord_984349) baseStart_984349 baseEnd_984349 := by
    simpa [prefixWord, tailWord_984349, baseEnd_984349] using wordTrace_append hprefix tailTrace_984349
  have hstable : (prefixWord ++ tailWord_984349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984349).length < 2 ^ (prefixWord ++ tailWord_984349).sum := by decide
  have hdescent : baseEnd_984349 < baseStart_984349 := by decide
  rcases family_descends (prefixWord ++ tailWord_984349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984352 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 3]
def baseStart_984352 : Nat := 118140960795 + 984352 * 2 ^ 59
def prefixEnd_984352 : Nat := 4983230072969 + 3 ^ 40 * 984352 * 2
def baseEnd_984352 : Nat := 449285074857455957309381

theorem tailTrace_984352 : CollatzResearch.WordTrace tailWord_984352 prefixEnd_984352 449285074857455957309381 := by
  unfold tailWord_984352
  simp only [CollatzResearch.WordTrace]
  refine ⟨17951133464934146391237655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23934844619912195188316873 17951133464934146391237655)
  ·
    refine ⟨26926700197401219586856483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17951133464934146391237655 26926700197401219586856483)
    ·
      refine ⟨40390050296101829380284725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26926700197401219586856483 40390050296101829380284725)
      ·
        refine ⟨3786567215259546504401693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40390050296101829380284725 3786567215259546504401693)
        ·
          refine ⟨1419962705722329939150635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3786567215259546504401693 1419962705722329939150635)
          ·
            refine ⟨2129944058583494908725953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419962705722329939150635 2129944058583494908725953)
            ·
              refine ⟨1597458043937621181544465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2129944058583494908725953 1597458043937621181544465)
              ·
                refine ⟨1198093532953215886158349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597458043937621181544465 1198093532953215886158349)
                ·
                  refine ⟨449285074857455957309381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198093532953215886158349 449285074857455957309381)
                  ·
                    rfl

theorem cell20_984352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_984352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984352 prefixEnd_984352 := by exact prefixLift 984352
  have htrace : WordTrace (prefixWord ++ tailWord_984352) baseStart_984352 baseEnd_984352 := by
    simpa [prefixWord, tailWord_984352, baseEnd_984352] using wordTrace_append hprefix tailTrace_984352
  have hstable : (prefixWord ++ tailWord_984352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984352).length < 2 ^ (prefixWord ++ tailWord_984352).sum := by decide
  have hdescent : baseEnd_984352 < baseStart_984352 := by decide
  rcases family_descends (prefixWord ++ tailWord_984352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984373 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 3]
def baseStart_984373 : Nat := 118140960795 + 984373 * 2 ^ 59
def prefixEnd_984373 : Nat := 4983230072969 + 3 ^ 40 * 984373 * 2
def baseEnd_984373 : Nat := 449294659829673217609295

theorem tailTrace_984373 : CollatzResearch.WordTrace tailWord_984373 prefixEnd_984373 449294659829673217609295 := by
  unfold tailWord_984373
  simp only [CollatzResearch.WordTrace]
  refine ⟨35903032862792213368989773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23935355241861475579326515 35903032862792213368989773)
  ·
    refine ⟨13463637323547080013371165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35903032862792213368989773 13463637323547080013371165)
    ·
      refine ⟨5048863996330155005014187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13463637323547080013371165 5048863996330155005014187)
      ·
        refine ⟨7573295994495232507521281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048863996330155005014187 7573295994495232507521281)
        ·
          refine ⟨5679971995871424380640961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7573295994495232507521281 5679971995871424380640961)
          ·
            refine ⟨4259978996903568285480721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5679971995871424380640961 4259978996903568285480721)
            ·
              refine ⟨3194984247677676214110541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259978996903568285480721 3194984247677676214110541)
              ·
                refine ⟨1198119092879128580291453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3194984247677676214110541 1198119092879128580291453)
                ·
                  refine ⟨449294659829673217609295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198119092879128580291453 449294659829673217609295)
                  ·
                    rfl

theorem cell20_984373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_984373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984373 prefixEnd_984373 := by exact prefixLift 984373
  have htrace : WordTrace (prefixWord ++ tailWord_984373) baseStart_984373 baseEnd_984373 := by
    simpa [prefixWord, tailWord_984373, baseEnd_984373] using wordTrace_append hprefix tailTrace_984373
  have hstable : (prefixWord ++ tailWord_984373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984373).length < 2 ^ (prefixWord ++ tailWord_984373).sum := by decide
  have hdescent : baseEnd_984373 < baseStart_984373 := by decide
  rcases family_descends (prefixWord ++ tailWord_984373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984380 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_984380 : Nat := 118140960795 + 984380 * 2 ^ 59
def prefixEnd_984380 : Nat := 4983230072969 + 3 ^ 40 * 984380 * 2
def baseEnd_984380 : Nat := 449297854820412304375933

theorem tailTrace_984380 : CollatzResearch.WordTrace tailWord_984380 prefixEnd_984380 449297854820412304375933 := by
  unfold tailWord_984380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17951644086883426782247297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23935525449177902376329729 17951644086883426782247297)
  ·
    refine ⟨13463733065162570086685473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17951644086883426782247297 13463733065162570086685473)
    ·
      refine ⟨10097799798871927565014105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13463733065162570086685473 10097799798871927565014105)
      ·
        refine ⟨7573349849153945673760579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10097799798871927565014105 7573349849153945673760579)
        ·
          refine ⟨11360024773730918510640869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7573349849153945673760579 11360024773730918510640869)
          ·
            refine ⟨2130004645074547220745163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11360024773730918510640869 2130004645074547220745163)
            ·
              refine ⟨3195006967611820831117745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130004645074547220745163 3195006967611820831117745)
              ·
                refine ⟨2396255225708865623338309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195006967611820831117745 2396255225708865623338309)
                ·
                  refine ⟨449297854820412304375933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396255225708865623338309 449297854820412304375933)
                  ·
                    rfl

theorem cell20_984380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_984380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984380 prefixEnd_984380 := by exact prefixLift 984380
  have htrace : WordTrace (prefixWord ++ tailWord_984380) baseStart_984380 baseEnd_984380 := by
    simpa [prefixWord, tailWord_984380, baseEnd_984380] using wordTrace_append hprefix tailTrace_984380
  have hstable : (prefixWord ++ tailWord_984380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984380).length < 2 ^ (prefixWord ++ tailWord_984380).sum := by decide
  have hdescent : baseEnd_984380 < baseStart_984380 := by decide
  rcases family_descends (prefixWord ++ tailWord_984380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984401 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_984401 : Nat := 118140960795 + 984401 * 2 ^ 59
def prefixEnd_984401 : Nat := 4983230072969 + 3 ^ 40 * 984401 * 2
def baseEnd_984401 : Nat := 449307439792629564675847

theorem tailTrace_984401 : CollatzResearch.WordTrace tailWord_984401 prefixEnd_984401 449307439792629564675847 := by
  unfold tailWord_984401
  simp only [CollatzResearch.WordTrace]
  refine ⟨35904054106690774151009057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23936036071127182767339371 35904054106690774151009057)
  ·
    refine ⟨26928040580018080613256793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35904054106690774151009057 26928040580018080613256793)
    ·
      refine ⟨20196030435013560459942595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26928040580018080613256793 20196030435013560459942595)
      ·
        refine ⟨30294045652520340689913893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20196030435013560459942595 30294045652520340689913893)
        ·
          refine ⟨5680133559847563879358855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30294045652520340689913893 5680133559847563879358855)
          ·
            refine ⟨8520200339771345819038283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5680133559847563879358855 8520200339771345819038283)
            ·
              refine ⟨12780300509657018728557425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8520200339771345819038283 12780300509657018728557425)
              ·
                refine ⟨9585225382242764046418069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12780300509657018728557425 9585225382242764046418069)
                ·
                  refine ⟨449307439792629564675847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9585225382242764046418069 449307439792629564675847)
                  ·
                    rfl

theorem cell20_984401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_984401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984401 prefixEnd_984401 := by exact prefixLift 984401
  have htrace : WordTrace (prefixWord ++ tailWord_984401) baseStart_984401 baseEnd_984401 := by
    simpa [prefixWord, tailWord_984401, baseEnd_984401] using wordTrace_append hprefix tailTrace_984401
  have hstable : (prefixWord ++ tailWord_984401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984401).length < 2 ^ (prefixWord ++ tailWord_984401).sum := by decide
  have hdescent : baseEnd_984401 < baseStart_984401 := by decide
  rcases family_descends (prefixWord ++ tailWord_984401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984408 : List Nat := [2, 1, 2, 2, 1, 1, 11]
def baseStart_984408 : Nat := 118140960795 + 984408 * 2 ^ 59
def prefixEnd_984408 : Nat := 4983230072969 + 3 ^ 40 * 984408 * 2
def baseEnd_984408 : Nat := 49923403864818739049165

theorem tailTrace_984408 : CollatzResearch.WordTrace tailWord_984408 prefixEnd_984408 49923403864818739049165 := by
  unfold tailWord_984408
  simp only [CollatzResearch.WordTrace]
  refine ⟨17952154708832707173256939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23936206278443609564342585 17952154708832707173256939)
  ·
    refine ⟨26928232063249060759885409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17952154708832707173256939 26928232063249060759885409)
    ·
      refine ⟨20196174047436795569914057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26928232063249060759885409 20196174047436795569914057)
      ·
        refine ⟨15147130535577596677435543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20196174047436795569914057 15147130535577596677435543)
        ·
          refine ⟨22720695803366395016153315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15147130535577596677435543 22720695803366395016153315)
          ·
            refine ⟨34081043705049592524229973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22720695803366395016153315 34081043705049592524229973)
            ·
              refine ⟨49923403864818739049165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34081043705049592524229973 49923403864818739049165)
              ·
                rfl

theorem cell20_984408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 11].length) (baseStart_984408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984408 prefixEnd_984408 := by exact prefixLift 984408
  have htrace : WordTrace (prefixWord ++ tailWord_984408) baseStart_984408 baseEnd_984408 := by
    simpa [prefixWord, tailWord_984408, baseEnd_984408] using wordTrace_append hprefix tailTrace_984408
  have hstable : (prefixWord ++ tailWord_984408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984408).length < 2 ^ (prefixWord ++ tailWord_984408).sum := by decide
  have hdescent : baseEnd_984408 < baseStart_984408 := by decide
  rcases family_descends (prefixWord ++ tailWord_984408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984428 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 3]
def baseStart_984428 : Nat := 118140960795 + 984428 * 2 ^ 59
def prefixEnd_984428 : Nat := 4983230072969 + 3 ^ 40 * 984428 * 2
def baseEnd_984428 : Nat := 449319763328337470775737

theorem tailTrace_984428 : CollatzResearch.WordTrace tailWord_984428 prefixEnd_984428 449319763328337470775737 := by
  unfold tailWord_984428
  simp only [CollatzResearch.WordTrace]
  refine ⟨17952519438796478881120969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23936692585061971841494625 17952519438796478881120969)
  ·
    refine ⟨13464389579097359160840727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17952519438796478881120969 13464389579097359160840727)
    ·
      refine ⟨20196584368646038741261091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13464389579097359160840727 20196584368646038741261091)
      ·
        refine ⟨30294876552969058111891637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20196584368646038741261091 30294876552969058111891637)
        ·
          refine ⟨2840144676840849197989841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30294876552969058111891637 2840144676840849197989841)
          ·
            refine ⟨2130108507630636898492381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840144676840849197989841 2130108507630636898492381)
            ·
              refine ⟨798790690361488836934643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2130108507630636898492381 798790690361488836934643)
              ·
                refine ⟨1198186035542233255401965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798790690361488836934643 1198186035542233255401965)
                ·
                  refine ⟨449319763328337470775737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198186035542233255401965 449319763328337470775737)
                  ·
                    rfl

theorem cell20_984428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_984428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984428 prefixEnd_984428 := by exact prefixLift 984428
  have htrace : WordTrace (prefixWord ++ tailWord_984428) baseStart_984428 baseEnd_984428 := by
    simpa [prefixWord, tailWord_984428, baseEnd_984428] using wordTrace_append hprefix tailTrace_984428
  have hstable : (prefixWord ++ tailWord_984428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984428).length < 2 ^ (prefixWord ++ tailWord_984428).sum := by decide
  have hdescent : baseEnd_984428 < baseStart_984428 := by decide
  rcases family_descends (prefixWord ++ tailWord_984428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984439 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_984439 : Nat := 118140960795 + 984439 * 2 ^ 59
def prefixEnd_984439 : Nat := 4983230072969 + 3 ^ 40 * 984439 * 2
def baseEnd_984439 : Nat := 449324784028070321409025

theorem tailTrace_984439 : CollatzResearch.WordTrace tailWord_984439 prefixEnd_984439 449324784028070321409025 := by
  unfold tailWord_984439
  simp only [CollatzResearch.WordTrace]
  refine ⟨35905440080553106640892371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23936960053702071093928247 35905440080553106640892371)
  ·
    refine ⟨53858160120829659961338557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35905440080553106640892371 53858160120829659961338557)
    ·
      refine ⟨20196810045311122485501959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53858160120829659961338557 20196810045311122485501959)
      ·
        refine ⟨30295215067966683728252939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20196810045311122485501959 30295215067966683728252939)
        ·
          refine ⟨45442822601950025592379409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30295215067966683728252939 45442822601950025592379409)
          ·
            refine ⟨34082116951462519194284557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45442822601950025592379409 34082116951462519194284557)
            ·
              refine ⟨12780793856798444697856709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34082116951462519194284557 12780793856798444697856709)
              ·
                refine ⟨2396398848149708380848133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12780793856798444697856709 2396398848149708380848133)
                ·
                  refine ⟨449324784028070321409025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396398848149708380848133 449324784028070321409025)
                  ·
                    rfl

theorem cell20_984439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_984439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984439 prefixEnd_984439 := by exact prefixLift 984439
  have htrace : WordTrace (prefixWord ++ tailWord_984439) baseStart_984439 baseEnd_984439 := by
    simpa [prefixWord, tailWord_984439, baseEnd_984439] using wordTrace_append hprefix tailTrace_984439
  have hstable : (prefixWord ++ tailWord_984439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984439).length < 2 ^ (prefixWord ++ tailWord_984439).sum := by decide
  have hdescent : baseEnd_984439 < baseStart_984439 := by decide
  rcases family_descends (prefixWord ++ tailWord_984439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984452 : List Nat := [2, 3, 2, 1, 1, 5, 1, 3, 2]
def baseStart_984452 : Nat := 118140960795 + 984452 * 2 ^ 59
def prefixEnd_984452 : Nat := 4983230072969 + 3 ^ 40 * 984452 * 2
def baseEnd_984452 : Nat := 449330717582300053975639

theorem tailTrace_984452 : CollatzResearch.WordTrace tailWord_984452 prefixEnd_984452 449330717582300053975639 := by
  unfold tailWord_984452
  simp only [CollatzResearch.WordTrace]
  refine ⟨17952957114753004930557805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23937276153004006574077073 17952957114753004930557805)
  ·
    refine ⟨6732358918032376848959177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17952957114753004930557805 6732358918032376848959177)
    ·
      refine ⟨5049269188524282636719383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6732358918032376848959177 5049269188524282636719383)
      ·
        refine ⟨7573903782786423955079075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5049269188524282636719383 7573903782786423955079075)
        ·
          refine ⟨11360855674179635932618613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7573903782786423955079075 11360855674179635932618613)
          ·
            refine ⟨1065080219454340868682995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11360855674179635932618613 1065080219454340868682995)
            ·
              refine ⟨1597620329181511303024493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065080219454340868682995 1597620329181511303024493)
              ·
                refine ⟨599107623443066738634185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597620329181511303024493 599107623443066738634185)
                ·
                  refine ⟨449330717582300053975639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599107623443066738634185 449330717582300053975639)
                  ·
                    rfl

theorem cell20_984452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_984452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984452 prefixEnd_984452 := by exact prefixLift 984452
  have htrace : WordTrace (prefixWord ++ tailWord_984452) baseStart_984452 baseEnd_984452 := by
    simpa [prefixWord, tailWord_984452, baseEnd_984452] using wordTrace_append hprefix tailTrace_984452
  have hstable : (prefixWord ++ tailWord_984452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984452).length < 2 ^ (prefixWord ++ tailWord_984452).sum := by decide
  have hdescent : baseEnd_984452 < baseStart_984452 := by decide
  rcases family_descends (prefixWord ++ tailWord_984452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984487 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 3]
def baseStart_984487 : Nat := 118140960795 + 984487 * 2 ^ 59
def prefixEnd_984487 : Nat := 4983230072969 + 3 ^ 40 * 984487 * 2
def baseEnd_984487 : Nat := 449346692535995487808829

theorem tailTrace_984487 : CollatzResearch.WordTrace tailWord_984487 prefixEnd_984487 449346692535995487808829 := by
  unfold tailWord_984487
  simp only [CollatzResearch.WordTrace]
  refine ⟨35907190784379210838639715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23938127189586140559093143 35907190784379210838639715)
  ·
    refine ⟨53860786176568816257959573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35907190784379210838639715 53860786176568816257959573)
    ·
      refine ⟨2524724352026663262091855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53860786176568816257959573 2524724352026663262091855)
      ·
        refine ⟨3787086528039994893137783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2524724352026663262091855 3787086528039994893137783)
        ·
          refine ⟨5680629792059992339706675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787086528039994893137783 5680629792059992339706675)
          ·
            refine ⟨8520944688089988509560013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5680629792059992339706675 8520944688089988509560013)
            ·
              refine ⟨3195354258033745691085005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8520944688089988509560013 3195354258033745691085005)
              ·
                refine ⟨1198257846762654634156877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3195354258033745691085005 1198257846762654634156877)
                ·
                  refine ⟨449346692535995487808829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198257846762654634156877 449346692535995487808829)
                  ·
                    rfl

theorem cell20_984487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 3].length) (baseStart_984487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984487 prefixEnd_984487 := by exact prefixLift 984487
  have htrace : WordTrace (prefixWord ++ tailWord_984487) baseStart_984487 baseEnd_984487 := by
    simpa [prefixWord, tailWord_984487, baseEnd_984487] using wordTrace_append hprefix tailTrace_984487
  have hstable : (prefixWord ++ tailWord_984487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984487).length < 2 ^ (prefixWord ++ tailWord_984487).sum := by decide
  have hdescent : baseEnd_984487 < baseStart_984487 := by decide
  rcases family_descends (prefixWord ++ tailWord_984487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984501 : List Nat := [1, 3, 3, 2, 2, 1, 2, 6]
def baseStart_984501 : Nat := 118140960795 + 984501 * 2 ^ 59
def prefixEnd_984501 : Nat := 4983230072969 + 3 ^ 40 * 984501 * 2
def baseEnd_984501 : Nat := 149784360839157887114035

theorem tailTrace_984501 : CollatzResearch.WordTrace tailWord_984501 prefixEnd_984501 149784360839157887114035 := by
  unfold tailWord_984501
  simp only [CollatzResearch.WordTrace]
  refine ⟨35907701406328491229649357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23938467604218994153099571 35907701406328491229649357)
  ·
    refine ⟨13465388027373184211118509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35907701406328491229649357 13465388027373184211118509)
    ·
      refine ⟨5049520510264944079169441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13465388027373184211118509 5049520510264944079169441)
      ·
        refine ⟨3787140382698708059377081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5049520510264944079169441 3787140382698708059377081)
        ·
          refine ⟨2840355287024031044532811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787140382698708059377081 2840355287024031044532811)
          ·
            refine ⟨4260532930536046566799217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840355287024031044532811 4260532930536046566799217)
            ·
              refine ⟨3195399697902034925099413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4260532930536046566799217 3195399697902034925099413)
              ·
                refine ⟨149784360839157887114035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3195399697902034925099413 149784360839157887114035)
                ·
                  rfl

theorem cell20_984501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_984501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984501 prefixEnd_984501 := by exact prefixLift 984501
  have htrace : WordTrace (prefixWord ++ tailWord_984501) baseStart_984501 baseEnd_984501 := by
    simpa [prefixWord, tailWord_984501, baseEnd_984501] using wordTrace_append hprefix tailTrace_984501
  have hstable : (prefixWord ++ tailWord_984501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984501).length < 2 ^ (prefixWord ++ tailWord_984501).sum := by decide
  have hdescent : baseEnd_984501 < baseStart_984501 := by decide
  rcases family_descends (prefixWord ++ tailWord_984501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984514 : List Nat := [3, 5, 2, 1, 1, 8]
def baseStart_984514 : Nat := 118140960795 + 984514 * 2 ^ 59
def prefixEnd_984514 : Nat := 4983230072969 + 3 ^ 40 * 984514 * 2
def baseEnd_984514 : Nat := 16642926521174199774397

theorem tailTrace_984514 : CollatzResearch.WordTrace tailWord_984514 prefixEnd_984514 16642926521174199774397 := by
  unfold tailWord_984514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977043888820348612468149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23938783703520929633248397 8977043888820348612468149)
  ·
    refine ⟨841597864576907682418889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8977043888820348612468149 841597864576907682418889)
    ·
      refine ⟨631198398432680761814167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 841597864576907682418889 631198398432680761814167)
      ·
        refine ⟨946797597649021142721251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631198398432680761814167 946797597649021142721251)
        ·
          refine ⟨1420196396473531714081877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946797597649021142721251 1420196396473531714081877)
          ·
            refine ⟨16642926521174199774397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1420196396473531714081877 16642926521174199774397)
            ·
              rfl

theorem cell20_984514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 8].length) (baseStart_984514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984514 prefixEnd_984514 := by exact prefixLift 984514
  have htrace : WordTrace (prefixWord ++ tailWord_984514) baseStart_984514 baseEnd_984514 := by
    simpa [prefixWord, tailWord_984514, baseEnd_984514] using wordTrace_append hprefix tailTrace_984514
  have hstable : (prefixWord ++ tailWord_984514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984514).length < 2 ^ (prefixWord ++ tailWord_984514).sum := by decide
  have hdescent : baseEnd_984514 < baseStart_984514 := by decide
  rcases family_descends (prefixWord ++ tailWord_984514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984522 : List Nat := [3, 1, 2, 1, 2, 11]
def baseStart_984522 : Nat := 118140960795 + 984522 * 2 ^ 59
def prefixEnd_984522 : Nat := 4983230072969 + 3 ^ 40 * 984522 * 2
def baseEnd_984522 : Nat := 16643061758877441542297

theorem tailTrace_984522 : CollatzResearch.WordTrace tailWord_984522 prefixEnd_984522 16643061758877441542297 := by
  unfold tailWord_984522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977116834813102954040955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23938978226168274544109213 8977116834813102954040955)
  ·
    refine ⟨13465675252219654431061433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8977116834813102954040955 13465675252219654431061433)
    ·
      refine ⟨10099256439164740823296075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13465675252219654431061433 10099256439164740823296075)
      ·
        refine ⟨15148884658747111234944113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10099256439164740823296075 15148884658747111234944113)
        ·
          refine ⟨11361663494060333426208085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15148884658747111234944113 11361663494060333426208085)
          ·
            refine ⟨16643061758877441542297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11361663494060333426208085 16643061758877441542297)
            ·
              rfl

theorem cell20_984522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 11].length) (baseStart_984522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984522 prefixEnd_984522 := by exact prefixLift 984522
  have htrace : WordTrace (prefixWord ++ tailWord_984522) baseStart_984522 baseEnd_984522 := by
    simpa [prefixWord, tailWord_984522, baseEnd_984522] using wordTrace_append hprefix tailTrace_984522
  have hstable : (prefixWord ++ tailWord_984522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984522).length < 2 ^ (prefixWord ++ tailWord_984522).sum := by decide
  have hdescent : baseEnd_984522 < baseStart_984522 := by decide
  rcases family_descends (prefixWord ++ tailWord_984522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984566 : List Nat := [5, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_984566 : Nat := 118140960795 + 984566 * 2 ^ 59
def prefixEnd_984566 : Nat := 4983230072969 + 3 ^ 40 * 984566 * 2
def baseEnd_984566 : Nat := 449382750288622324175173

theorem tailTrace_984566 : CollatzResearch.WordTrace tailWord_984566 prefixEnd_984566 449382750288622324175173 := by
  unfold tailWord_984566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244379509443312958172847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23940048100728671553843701 2244379509443312958172847)
  ·
    refine ⟨3366569264164969437259271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2244379509443312958172847 3366569264164969437259271)
    ·
      refine ⟨5049853896247454155888907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3366569264164969437259271 5049853896247454155888907)
      ·
        refine ⟨7574780844371181233833361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5049853896247454155888907 7574780844371181233833361)
        ·
          refine ⟨5681085633278385925375021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7574780844371181233833361 5681085633278385925375021)
          ·
            refine ⟨2130407112479394722015633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5681085633278385925375021 2130407112479394722015633)
            ·
              refine ⟨1597805334359546041511725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130407112479394722015633 1597805334359546041511725)
              ·
                refine ⟨599177000384829765566897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597805334359546041511725 599177000384829765566897)
                ·
                  refine ⟨449382750288622324175173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599177000384829765566897 449382750288622324175173)
                  ·
                    rfl

theorem cell20_984566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_984566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984566 prefixEnd_984566 := by exact prefixLift 984566
  have htrace : WordTrace (prefixWord ++ tailWord_984566) baseStart_984566 baseEnd_984566 := by
    simpa [prefixWord, tailWord_984566, baseEnd_984566] using wordTrace_append hprefix tailTrace_984566
  have hstable : (prefixWord ++ tailWord_984566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984566).length < 2 ^ (prefixWord ++ tailWord_984566).sum := by decide
  have hdescent : baseEnd_984566 < baseStart_984566 := by decide
  rcases family_descends (prefixWord ++ tailWord_984566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984577 : List Nat := [1, 2, 4, 1, 4, 1, 7]
def baseStart_984577 : Nat := 118140960795 + 984577 * 2 ^ 59
def prefixEnd_984577 : Nat := 4983230072969 + 3 ^ 40 * 984577 * 2
def baseEnd_984577 : Nat := 49931974554261686089829

theorem tailTrace_984577 : CollatzResearch.WordTrace tailWord_984577 prefixEnd_984577 49931974554261686089829 := by
  unfold tailWord_984577
  simp only [CollatzResearch.WordTrace]
  refine ⟨35910473354053156209415985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23940315569368770806277323 35910473354053156209415985)
  ·
    refine ⟨26932855015539867157061989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35910473354053156209415985 26932855015539867157061989)
    ·
      refine ⟨5049910315413725091949123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26932855015539867157061989 5049910315413725091949123)
      ·
        refine ⟨7574865473120587637923685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5049910315413725091949123 7574865473120587637923685)
        ·
          refine ⟨1420287276210110182110691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7574865473120587637923685 1420287276210110182110691)
          ·
            refine ⟨2130430914315165273166037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420287276210110182110691 2130430914315165273166037)
            ·
              refine ⟨49931974554261686089829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2130430914315165273166037 49931974554261686089829)
              ·
                rfl

theorem cell20_984577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 7].length) (baseStart_984577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984577 prefixEnd_984577 := by exact prefixLift 984577
  have htrace : WordTrace (prefixWord ++ tailWord_984577) baseStart_984577 baseEnd_984577 := by
    simpa [prefixWord, tailWord_984577, baseEnd_984577] using wordTrace_append hprefix tailTrace_984577
  have hstable : (prefixWord ++ tailWord_984577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984577).length < 2 ^ (prefixWord ++ tailWord_984577).sum := by decide
  have hdescent : baseEnd_984577 < baseStart_984577 := by decide
  rcases family_descends (prefixWord ++ tailWord_984577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984608 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_984608 : Nat := 118140960795 + 984608 * 2 ^ 59
def prefixEnd_984608 : Nat := 4983230072969 + 3 ^ 40 * 984608 * 2
def baseEnd_984608 : Nat := 449401920233056844775001

theorem tailTrace_984608 : CollatzResearch.WordTrace tailWord_984608 prefixEnd_984608 449401920233056844775001 := by
  unfold tailWord_984608
  simp only [CollatzResearch.WordTrace]
  refine ⟨17955802008470424251897239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23941069344627232335862985 17955802008470424251897239)
  ·
    refine ⟨26933703012705636377845859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17955802008470424251897239 26933703012705636377845859)
    ·
      refine ⟨40400554519058454566768789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26933703012705636377845859 40400554519058454566768789)
      ·
        refine ⟨1893775993080865057817287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40400554519058454566768789 1893775993080865057817287)
        ·
          refine ⟨2840663989621297586725931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893775993080865057817287 2840663989621297586725931)
          ·
            refine ⟨4260995984431946380088897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840663989621297586725931 4260995984431946380088897)
            ·
              refine ⟨3195746988323959785066673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4260995984431946380088897 3195746988323959785066673)
              ·
                refine ⟨2396810241242969838800005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195746988323959785066673 2396810241242969838800005)
                ·
                  refine ⟨449401920233056844775001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396810241242969838800005 449401920233056844775001)
                  ·
                    rfl

theorem cell20_984608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_984608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984608 prefixEnd_984608 := by exact prefixLift 984608
  have htrace : WordTrace (prefixWord ++ tailWord_984608) baseStart_984608 baseEnd_984608 := by
    simpa [prefixWord, tailWord_984608, baseEnd_984608] using wordTrace_append hprefix tailTrace_984608
  have hstable : (prefixWord ++ tailWord_984608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984608).length < 2 ^ (prefixWord ++ tailWord_984608).sum := by decide
  have hdescent : baseEnd_984608 < baseStart_984608 := by decide
  rcases family_descends (prefixWord ++ tailWord_984608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984611 : List Nat := [1, 1, 1, 4, 6, 1, 2, 4]
def baseStart_984611 : Nat := 118140960795 + 984611 * 2 ^ 59
def prefixEnd_984611 : Nat := 4983230072969 + 3 ^ 40 * 984611 * 2
def baseEnd_984611 : Nat := 149801096504934055891663

theorem tailTrace_984611 : CollatzResearch.WordTrace tailWord_984611 prefixEnd_984611 149801096504934055891663 := by
  unfold tailWord_984611
  simp only [CollatzResearch.WordTrace]
  refine ⟨35911713435929980016153687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23941142290619986677435791 35911713435929980016153687)
  ·
    refine ⟨53867570153894970024230531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35911713435929980016153687 53867570153894970024230531)
    ·
      refine ⟨80801355230842455036345797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53867570153894970024230531 80801355230842455036345797)
      ·
        refine ⟨15150254105782960319314837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80801355230842455036345797 15150254105782960319314837)
        ·
          refine ⟨710168161208576264967883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15150254105782960319314837 710168161208576264967883)
          ·
            refine ⟨1065252241812864397451825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710168161208576264967883 1065252241812864397451825)
            ·
              refine ⟨798939181359648298088869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065252241812864397451825 798939181359648298088869)
              ·
                refine ⟨149801096504934055891663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 798939181359648298088869 149801096504934055891663)
                ·
                  rfl

theorem cell20_984611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 4].length) (baseStart_984611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984611 prefixEnd_984611 := by exact prefixLift 984611
  have htrace : WordTrace (prefixWord ++ tailWord_984611) baseStart_984611 baseEnd_984611 := by
    simpa [prefixWord, tailWord_984611, baseEnd_984611] using wordTrace_append hprefix tailTrace_984611
  have hstable : (prefixWord ++ tailWord_984611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984611).length < 2 ^ (prefixWord ++ tailWord_984611).sum := by decide
  have hdescent : baseEnd_984611 < baseStart_984611 := by decide
  rcases family_descends (prefixWord ++ tailWord_984611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984681 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_984681 : Nat := 118140960795 + 984681 * 2 ^ 59
def prefixEnd_984681 : Nat := 4983230072969 + 3 ^ 40 * 984681 * 2
def baseEnd_984681 : Nat := 449435239422193035341369

theorem tailTrace_984681 : CollatzResearch.WordTrace tailWord_984681 prefixEnd_984681 449435239422193035341369 := by
  unfold tailWord_984681
  simp only [CollatzResearch.WordTrace]
  refine ⟨35914266545676381971201897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23942844363784254647467931 35914266545676381971201897)
  ·
    refine ⟨26935699909257286478401423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35914266545676381971201897 26935699909257286478401423)
    ·
      refine ⟨40403549863885929717602135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26935699909257286478401423 40403549863885929717602135)
      ·
        refine ⟨60605324795828894576403203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40403549863885929717602135 60605324795828894576403203)
        ·
          refine ⟨90907987193743341864604805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60605324795828894576403203 90907987193743341864604805)
          ·
            refine ⟨17045247598826876599613401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90907987193743341864604805 17045247598826876599613401)
            ·
              refine ⟨12783935699120157449710051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17045247598826876599613401 12783935699120157449710051)
              ·
                refine ⟨19175903548680236174565077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12783935699120157449710051 19175903548680236174565077)
                ·
                  refine ⟨449435239422193035341369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19175903548680236174565077 449435239422193035341369)
                  ·
                    rfl

theorem cell20_984681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_984681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984681 prefixEnd_984681 := by exact prefixLift 984681
  have htrace : WordTrace (prefixWord ++ tailWord_984681) baseStart_984681 baseEnd_984681 := by
    simpa [prefixWord, tailWord_984681, baseEnd_984681] using wordTrace_append hprefix tailTrace_984681
  have hstable : (prefixWord ++ tailWord_984681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984681).length < 2 ^ (prefixWord ++ tailWord_984681).sum := by decide
  have hdescent : baseEnd_984681 < baseStart_984681 := by decide
  rcases family_descends (prefixWord ++ tailWord_984681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984684 : List Nat := [2, 2, 1, 1, 3, 1, 1, 7, 2]
def baseStart_984684 : Nat := 118140960795 + 984684 * 2 ^ 59
def prefixEnd_984684 : Nat := 4983230072969 + 3 ^ 40 * 984684 * 2
def baseEnd_984684 : Nat := 449436608703938358241357

theorem tailTrace_984684 : CollatzResearch.WordTrace tailWord_984684 prefixEnd_984684 449436608703938358241357 := by
  unfold tailWord_984684
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957187982332756741780553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23942917309777008989040737 17957187982332756741780553)
  ·
    refine ⟨13467890986749567556335415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17957187982332756741780553 13467890986749567556335415)
    ·
      refine ⟨20201836480124351334503123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13467890986749567556335415 20201836480124351334503123)
      ·
        refine ⟨30302754720186527001754685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20201836480124351334503123 30302754720186527001754685)
        ·
          refine ⟨11363533020069947625658007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30302754720186527001754685 11363533020069947625658007)
          ·
            refine ⟨17045299530104921438487011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11363533020069947625658007 17045299530104921438487011)
            ·
              refine ⟨25567949295157382157730517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17045299530104921438487011 25567949295157382157730517)
              ·
                refine ⟨599248811605251144321809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25567949295157382157730517 599248811605251144321809)
                ·
                  refine ⟨449436608703938358241357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599248811605251144321809 449436608703938358241357)
                  ·
                    rfl

theorem cell20_984684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_984684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984684 prefixEnd_984684 := by exact prefixLift 984684
  have htrace : WordTrace (prefixWord ++ tailWord_984684) baseStart_984684 baseEnd_984684 := by
    simpa [prefixWord, tailWord_984684, baseEnd_984684] using wordTrace_append hprefix tailTrace_984684
  have hstable : (prefixWord ++ tailWord_984684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984684).length < 2 ^ (prefixWord ++ tailWord_984684).sum := by decide
  have hdescent : baseEnd_984684 < baseStart_984684 := by decide
  rcases family_descends (prefixWord ++ tailWord_984684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984694 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_984694 : Nat := 118140960795 + 984694 * 2 ^ 59
def prefixEnd_984694 : Nat := 4983230072969 + 3 ^ 40 * 984694 * 2
def baseEnd_984694 : Nat := 449441172976422767907983

theorem tailTrace_984694 : CollatzResearch.WordTrace tailWord_984694 prefixEnd_984694 449441172976422767907983 := by
  unfold tailWord_984694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244671293414330324464071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23943160463086190127616757 2244671293414330324464071)
  ·
    refine ⟨3367006940121495486696107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2244671293414330324464071 3367006940121495486696107)
    ·
      refine ⟨5050510410182243230044161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3367006940121495486696107 5050510410182243230044161)
      ·
        refine ⟨3787882807636682422533121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5050510410182243230044161 3787882807636682422533121)
        ·
          refine ⟨2840912105727511816899841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787882807636682422533121 2840912105727511816899841)
          ·
            refine ⟨2130684079295633862674881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840912105727511816899841 2130684079295633862674881)
            ·
              refine ⟨1598013059471725397006161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130684079295633862674881 1598013059471725397006161)
              ·
                refine ⟨1198509794603794047754621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1598013059471725397006161 1198509794603794047754621)
                ·
                  refine ⟨449441172976422767907983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198509794603794047754621 449441172976422767907983)
                  ·
                    rfl

theorem cell20_984694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_984694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984694 prefixEnd_984694 := by exact prefixLift 984694
  have htrace : WordTrace (prefixWord ++ tailWord_984694) baseStart_984694 baseEnd_984694 := by
    simpa [prefixWord, tailWord_984694, baseEnd_984694] using wordTrace_append hprefix tailTrace_984694
  have hstable : (prefixWord ++ tailWord_984694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984694).length < 2 ^ (prefixWord ++ tailWord_984694).sum := by decide
  have hdescent : baseEnd_984694 < baseStart_984694 := by decide
  rcases family_descends (prefixWord ++ tailWord_984694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984701 : List Nat := [1, 4, 1, 1, 4, 2, 1, 4, 2]
def baseStart_984701 : Nat := 118140960795 + 984701 * 2 ^ 59
def prefixEnd_984701 : Nat := 4983230072969 + 3 ^ 40 * 984701 * 2
def baseEnd_984701 : Nat := 449444367967161854674621

theorem tailTrace_984701 : CollatzResearch.WordTrace tailWord_984701 prefixEnd_984701 449444367967161854674621 := by
  unfold tailWord_984701
  simp only [CollatzResearch.WordTrace]
  refine ⟨35914996005603925386929957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23943330670402616924619971 35914996005603925386929957)
  ·
    refine ⟨6734061751050736010049367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35914996005603925386929957 6734061751050736010049367)
    ·
      refine ⟨10101092626576104015074051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6734061751050736010049367 10101092626576104015074051)
      ·
        refine ⟨15151638939864156022611077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10101092626576104015074051 15151638939864156022611077)
        ·
          refine ⟨2840932301224529254239577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15151638939864156022611077 2840932301224529254239577)
          ·
            refine ⟨2130699225918396940679683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840932301224529254239577 2130699225918396940679683)
            ·
              refine ⟨3196048838877595411019525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130699225918396940679683 3196048838877595411019525)
              ·
                refine ⟨599259157289549139566161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3196048838877595411019525 599259157289549139566161)
                ·
                  refine ⟨449444367967161854674621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599259157289549139566161 449444367967161854674621)
                  ·
                    rfl

theorem cell20_984701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_984701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984701 prefixEnd_984701 := by exact prefixLift 984701
  have htrace : WordTrace (prefixWord ++ tailWord_984701) baseStart_984701 baseEnd_984701 := by
    simpa [prefixWord, tailWord_984701, baseEnd_984701] using wordTrace_append hprefix tailTrace_984701
  have hstable : (prefixWord ++ tailWord_984701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984701).length < 2 ^ (prefixWord ++ tailWord_984701).sum := by decide
  have hdescent : baseEnd_984701 < baseStart_984701 := by decide
  rcases family_descends (prefixWord ++ tailWord_984701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984708 : List Nat := [2, 3, 2, 1, 4, 2, 1, 5]
def baseStart_984708 : Nat := 118140960795 + 984708 * 2 ^ 59
def prefixEnd_984708 : Nat := 4983230072969 + 3 ^ 40 * 984708 * 2
def baseEnd_984708 : Nat := 149815854319300313813753

theorem tailTrace_984708 : CollatzResearch.WordTrace tailWord_984708 prefixEnd_984708 149815854319300313813753 := by
  unfold tailWord_984708
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957625658289282791217389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23943500877719043721623185 17957625658289282791217389)
  ·
    refine ⟨6734109621858481046706521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17957625658289282791217389 6734109621858481046706521)
    ·
      refine ⟨5050582216393860785029891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6734109621858481046706521 5050582216393860785029891)
      ·
        refine ⟨7575873324590791177544837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5050582216393860785029891 7575873324590791177544837)
        ·
          refine ⟨1420476248360773345789657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7575873324590791177544837 1420476248360773345789657)
          ·
            refine ⟨1065357186270580009342243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1420476248360773345789657 1065357186270580009342243)
            ·
              refine ⟨1598035779405870014013365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065357186270580009342243 1598035779405870014013365)
              ·
                refine ⟨149815854319300313813753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1598035779405870014013365 149815854319300313813753)
                ·
                  rfl

theorem cell20_984708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_984708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984708 prefixEnd_984708 := by exact prefixLift 984708
  have htrace : WordTrace (prefixWord ++ tailWord_984708) baseStart_984708 baseEnd_984708 := by
    simpa [prefixWord, tailWord_984708, baseEnd_984708] using wordTrace_append hprefix tailTrace_984708
  have hstable : (prefixWord ++ tailWord_984708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984708).length < 2 ^ (prefixWord ++ tailWord_984708).sum := by decide
  have hdescent : baseEnd_984708 < baseStart_984708 := by decide
  rcases family_descends (prefixWord ++ tailWord_984708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984790 : List Nat := [5, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_984790 : Nat := 118140960795 + 984790 * 2 ^ 59
def prefixEnd_984790 : Nat := 4983230072969 + 3 ^ 40 * 984790 * 2
def baseEnd_984790 : Nat := 449484989992273100707591

theorem tailTrace_984790 : CollatzResearch.WordTrace tailWord_984790 prefixEnd_984790 449484989992273100707591 := by
  unfold tailWord_984790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244890131392593349182489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23945494734854329057946549 2244890131392593349182489)
  ·
    refine ⟨1683667598544445011886867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2244890131392593349182489 1683667598544445011886867)
    ·
      refine ⟨2525501397816667517830301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683667598544445011886867 2525501397816667517830301)
      ·
        refine ⟨947063024181250319186363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2525501397816667517830301 947063024181250319186363)
        ·
          refine ⟨1420594536271875478779545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947063024181250319186363 1420594536271875478779545)
          ·
            refine ⟨1065445902203906609084659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1420594536271875478779545 1065445902203906609084659)
            ·
              refine ⟨1598168853305859913626989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065445902203906609084659 1598168853305859913626989)
              ·
                refine ⟨599313319989697467610121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1598168853305859913626989 599313319989697467610121)
                ·
                  refine ⟨449484989992273100707591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599313319989697467610121 449484989992273100707591)
                  ·
                    rfl

theorem cell20_984790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_984790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984790 prefixEnd_984790 := by exact prefixLift 984790
  have htrace : WordTrace (prefixWord ++ tailWord_984790) baseStart_984790 baseEnd_984790 := by
    simpa [prefixWord, tailWord_984790, baseEnd_984790] using wordTrace_append hprefix tailTrace_984790
  have hstable : (prefixWord ++ tailWord_984790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984790).length < 2 ^ (prefixWord ++ tailWord_984790).sum := by decide
  have hdescent : baseEnd_984790 < baseStart_984790 := by decide
  rcases family_descends (prefixWord ++ tailWord_984790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984815 : List Nat := [1, 1, 2, 1, 5, 1, 5, 2, 2]
def baseStart_984815 : Nat := 118140960795 + 984815 * 2 ^ 59
def prefixEnd_984815 : Nat := 4983230072969 + 3 ^ 40 * 984815 * 2
def baseEnd_984815 : Nat := 449496400673484124874155

theorem tailTrace_984815 : CollatzResearch.WordTrace tailWord_984815 prefixEnd_984815 449496400673484124874155 := by
  unfold tailWord_984815
  simp only [CollatzResearch.WordTrace]
  refine ⟨35919153927190922856579899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23946102618127281904386599 35919153927190922856579899)
  ·
    refine ⟨53878730890786384284869849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35919153927190922856579899 53878730890786384284869849)
    ·
      refine ⟨40409048168089788213652387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53878730890786384284869849 40409048168089788213652387)
      ·
        refine ⟨60613572252134682320478581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40409048168089788213652387 60613572252134682320478581)
        ·
          refine ⟨5682522398637626467544867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60613572252134682320478581 5682522398637626467544867)
          ·
            refine ⟨8523783597956439701317301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5682522398637626467544867 8523783597956439701317301)
            ·
              refine ⟨799104712308416221998497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8523783597956439701317301 799104712308416221998497)
              ·
                refine ⟨599328534231312166498873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799104712308416221998497 599328534231312166498873)
                ·
                  refine ⟨449496400673484124874155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599328534231312166498873 449496400673484124874155)
                  ·
                    rfl

theorem cell20_984815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 2].length) (baseStart_984815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984815 prefixEnd_984815 := by exact prefixLift 984815
  have htrace : WordTrace (prefixWord ++ tailWord_984815) baseStart_984815 baseEnd_984815 := by
    simpa [prefixWord, tailWord_984815, baseEnd_984815] using wordTrace_append hprefix tailTrace_984815
  have hstable : (prefixWord ++ tailWord_984815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984815).length < 2 ^ (prefixWord ++ tailWord_984815).sum := by decide
  have hdescent : baseEnd_984815 < baseStart_984815 := by decide
  rcases family_descends (prefixWord ++ tailWord_984815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984819 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 4]
def baseStart_984819 : Nat := 118140960795 + 984819 * 2 ^ 59
def prefixEnd_984819 : Nat := 4983230072969 + 3 ^ 40 * 984819 * 2
def baseEnd_984819 : Nat := 449498226382477888740805

theorem tailTrace_984819 : CollatzResearch.WordTrace tailWord_984819 prefixEnd_984819 449498226382477888740805 := by
  unfold tailWord_984819
  simp only [CollatzResearch.WordTrace]
  refine ⟨35919299819176431539725511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23946199879450954359817007 35919299819176431539725511)
  ·
    refine ⟨53878949728764647309588267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35919299819176431539725511 53878949728764647309588267)
    ·
      refine ⟨80818424593146970964382401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53878949728764647309588267 80818424593146970964382401)
      ·
        refine ⟨60613818444860228223286801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80818424593146970964382401 60613818444860228223286801)
        ·
          refine ⟨45460363833645171167465101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60613818444860228223286801 45460363833645171167465101)
          ·
            refine ⟨17047636437616939187799413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45460363833645171167465101 17047636437616939187799413)
            ·
              refine ⟨1598215916026588048856195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17047636437616939187799413 1598215916026588048856195)
              ·
                refine ⟨2397323874039882073284293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598215916026588048856195 2397323874039882073284293)
                ·
                  refine ⟨449498226382477888740805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397323874039882073284293 449498226382477888740805)
                  ·
                    rfl

theorem cell20_984819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_984819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984819 prefixEnd_984819 := by exact prefixLift 984819
  have htrace : WordTrace (prefixWord ++ tailWord_984819) baseStart_984819 baseEnd_984819 := by
    simpa [prefixWord, tailWord_984819, baseEnd_984819] using wordTrace_append hprefix tailTrace_984819
  have hstable : (prefixWord ++ tailWord_984819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984819).length < 2 ^ (prefixWord ++ tailWord_984819).sum := by decide
  have hdescent : baseEnd_984819 < baseStart_984819 := by decide
  rcases family_descends (prefixWord ++ tailWord_984819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984881 : List Nat := [1, 2, 2, 3, 2, 4, 1, 5]
def baseStart_984881 : Nat := 118140960795 + 984881 * 2 ^ 59
def prefixEnd_984881 : Nat := 4983230072969 + 3 ^ 40 * 984881 * 2
def baseEnd_984881 : Nat := 149842174957293742891295

theorem tailTrace_984881 : CollatzResearch.WordTrace tailWord_984881 prefixEnd_984881 149842174957293742891295 := by
  unfold tailWord_984881
  simp only [CollatzResearch.WordTrace]
  refine ⟨35921561144951816128482497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23947707429967877418988331 35921561144951816128482497)
  ·
    refine ⟨26941170858713862096361873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35921561144951816128482497 26941170858713862096361873)
    ·
      refine ⟨20205878144035396572271405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26941170858713862096361873 20205878144035396572271405)
      ·
        refine ⟨7577204304013273714601777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20205878144035396572271405 7577204304013273714601777)
        ·
          refine ⟨5682903228009955285951333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7577204304013273714601777 5682903228009955285951333)
          ·
            refine ⟨1065544355251866616115875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5682903228009955285951333 1065544355251866616115875)
            ·
              refine ⟨1598316532877799924173813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065544355251866616115875 1598316532877799924173813)
              ·
                refine ⟨149842174957293742891295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1598316532877799924173813 149842174957293742891295)
                ·
                  rfl

theorem cell20_984881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 5].length) (baseStart_984881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984881 prefixEnd_984881 := by exact prefixLift 984881
  have htrace : WordTrace (prefixWord ++ tailWord_984881) baseStart_984881 baseEnd_984881 := by
    simpa [prefixWord, tailWord_984881, baseEnd_984881] using wordTrace_append hprefix tailTrace_984881
  have hstable : (prefixWord ++ tailWord_984881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984881).length < 2 ^ (prefixWord ++ tailWord_984881).sum := by decide
  have hdescent : baseEnd_984881 < baseStart_984881 := by decide
  rcases family_descends (prefixWord ++ tailWord_984881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984888 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 3]
def baseStart_984888 : Nat := 118140960795 + 984888 * 2 ^ 59
def prefixEnd_984888 : Nat := 4983230072969 + 3 ^ 40 * 984888 * 2
def baseEnd_984888 : Nat := 449529719862620315440523

theorem tailTrace_984888 : CollatzResearch.WordTrace tailWord_984888 prefixEnd_984888 449529719862620315440523 := by
  unfold tailWord_984888
  simp only [CollatzResearch.WordTrace]
  refine ⟨17960908227963228161993659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23947877637284304215991545 17960908227963228161993659)
  ·
    refine ⟨26941362341944842242990489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17960908227963228161993659 26941362341944842242990489)
    ·
      refine ⟨20206021756458631682242867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26941362341944842242990489 20206021756458631682242867)
      ·
        refine ⟨30309032634687947523364301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20206021756458631682242867 30309032634687947523364301)
        ·
          refine ⟨11365887238007980321261613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30309032634687947523364301 11365887238007980321261613)
          ·
            refine ⟨4262207714252992620473105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11365887238007980321261613 4262207714252992620473105)
            ·
              refine ⟨3196655785689744465354829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4262207714252992620473105 3196655785689744465354829)
              ·
                refine ⟨1198745919633654174508061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3196655785689744465354829 1198745919633654174508061)
                ·
                  refine ⟨449529719862620315440523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198745919633654174508061 449529719862620315440523)
                  ·
                    rfl

theorem cell20_984888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_984888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984888 prefixEnd_984888 := by exact prefixLift 984888
  have htrace : WordTrace (prefixWord ++ tailWord_984888) baseStart_984888 baseEnd_984888 := by
    simpa [prefixWord, tailWord_984888, baseEnd_984888] using wordTrace_append hprefix tailTrace_984888
  have hstable : (prefixWord ++ tailWord_984888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984888).length < 2 ^ (prefixWord ++ tailWord_984888).sum := by decide
  have hdescent : baseEnd_984888 < baseStart_984888 := by decide
  rcases family_descends (prefixWord ++ tailWord_984888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984974 : List Nat := [4, 1, 1, 5, 1, 2, 6]
def baseStart_984974 : Nat := 118140960795 + 984974 * 2 ^ 59
def prefixEnd_984974 : Nat := 4983230072969 + 3 ^ 40 * 984974 * 2
def baseEnd_984974 : Nat := 49952108067331804285945

theorem tailTrace_984974 : CollatzResearch.WordTrace tailWord_984974 prefixEnd_984974 49952108067331804285945 := by
  unfold tailWord_984974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490619141701861626452247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23949968755743262007745317 4490619141701861626452247)
  ·
    refine ⟨6735928712552792439678371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4490619141701861626452247 6735928712552792439678371)
    ·
      refine ⟨10103893068829188659517557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6735928712552792439678371 10103893068829188659517557)
      ·
        refine ⟨947239975202736436829771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10103893068829188659517557 947239975202736436829771)
        ·
          refine ⟨1420859962804104655244657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947239975202736436829771 1420859962804104655244657)
          ·
            refine ⟨1065644972103078491433493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1420859962804104655244657 1065644972103078491433493)
            ·
              refine ⟨49952108067331804285945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1065644972103078491433493 49952108067331804285945)
              ·
                rfl

theorem cell20_984974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 6].length) (baseStart_984974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984974 prefixEnd_984974 := by exact prefixLift 984974
  have htrace : WordTrace (prefixWord ++ tailWord_984974) baseStart_984974 baseEnd_984974 := by
    simpa [prefixWord, tailWord_984974, baseEnd_984974] using wordTrace_append hprefix tailTrace_984974
  have hstable : (prefixWord ++ tailWord_984974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984974).length < 2 ^ (prefixWord ++ tailWord_984974).sum := by decide
  have hdescent : baseEnd_984974 < baseStart_984974 := by decide
  rcases family_descends (prefixWord ++ tailWord_984974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984984 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 4]
def baseStart_984984 : Nat := 118140960795 + 984984 * 2 ^ 59
def prefixEnd_984984 : Nat := 4983230072969 + 3 ^ 40 * 984984 * 2
def baseEnd_984984 : Nat := 449573536878470648240131

theorem tailTrace_984984 : CollatzResearch.WordTrace tailWord_984984 prefixEnd_984984 449573536878470648240131 := by
  unfold tailWord_984984
  simp only [CollatzResearch.WordTrace]
  refine ⟨17962658931789332359741003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23950211909052443146321337 17962658931789332359741003)
  ·
    refine ⟨26943988397683998539611505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17962658931789332359741003 26943988397683998539611505)
    ·
      refine ⟨20207991298262998904708629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26943988397683998539611505 20207991298262998904708629)
      ·
        refine ⟨947249592106078073658217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20207991298262998904708629 947249592106078073658217)
        ·
          refine ⟨710437194079558555243663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 947249592106078073658217 710437194079558555243663)
          ·
            refine ⟨1065655791119337832865495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710437194079558555243663 1065655791119337832865495)
            ·
              refine ⟨1598483686679006749298243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065655791119337832865495 1598483686679006749298243)
              ·
                refine ⟨2397725530018510123947365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598483686679006749298243 2397725530018510123947365)
                ·
                  refine ⟨449573536878470648240131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397725530018510123947365 449573536878470648240131)
                  ·
                    rfl

theorem cell20_984984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_984984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984984 prefixEnd_984984 := by exact prefixLift 984984
  have htrace : WordTrace (prefixWord ++ tailWord_984984) baseStart_984984 baseEnd_984984 := by
    simpa [prefixWord, tailWord_984984, baseEnd_984984] using wordTrace_append hprefix tailTrace_984984
  have hstable : (prefixWord ++ tailWord_984984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984984).length < 2 ^ (prefixWord ++ tailWord_984984).sum := by decide
  have hdescent : baseEnd_984984 < baseStart_984984 := by decide
  rcases family_descends (prefixWord ++ tailWord_984984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984985 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_984985 : Nat := 118140960795 + 984985 * 2 ^ 59
def prefixEnd_984985 : Nat := 4983230072969 + 3 ^ 40 * 984985 * 2
def baseEnd_984985 : Nat := 449573993305719089206793

theorem tailTrace_984985 : CollatzResearch.WordTrace tailWord_984985 prefixEnd_984985 449573993305719089206793 := by
  unfold tailWord_984985
  simp only [CollatzResearch.WordTrace]
  refine ⟨35925354336575041890268409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23950236224383361260178939 35925354336575041890268409)
  ·
    refine ⟨26944015752431281417701307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35925354336575041890268409 26944015752431281417701307)
    ·
      refine ⟨40416023628646922126551961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26944015752431281417701307 40416023628646922126551961)
      ·
        refine ⟨30312017721485191594913971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40416023628646922126551961 30312017721485191594913971)
        ·
          refine ⟨45468026582227787392370957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30312017721485191594913971 45468026582227787392370957)
          ·
            refine ⟨17050509968335420272139109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45468026582227787392370957 17050509968335420272139109)
            ·
              refine ⟨3196970619062891301026083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17050509968335420272139109 3196970619062891301026083)
              ·
                refine ⟨4795455928594336951539125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196970619062891301026083 4795455928594336951539125)
                ·
                  refine ⟨449573993305719089206793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4795455928594336951539125 449573993305719089206793)
                  ·
                    rfl

theorem cell20_984985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_984985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984985 prefixEnd_984985 := by exact prefixLift 984985
  have htrace : WordTrace (prefixWord ++ tailWord_984985) baseStart_984985 baseEnd_984985 := by
    simpa [prefixWord, tailWord_984985, baseEnd_984985] using wordTrace_append hprefix tailTrace_984985
  have hstable : (prefixWord ++ tailWord_984985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984985).length < 2 ^ (prefixWord ++ tailWord_984985).sum := by decide
  have hdescent : baseEnd_984985 < baseStart_984985 := by decide
  rcases family_descends (prefixWord ++ tailWord_984985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984988 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_984988 : Nat := 118140960795 + 984988 * 2 ^ 59
def prefixEnd_984988 : Nat := 4983230072969 + 3 ^ 40 * 984988 * 2
def baseEnd_984988 : Nat := 449575362587464412106781

theorem tailTrace_984988 : CollatzResearch.WordTrace tailWord_984988 prefixEnd_984988 449575362587464412106781 := by
  unfold tailWord_984988
  simp only [CollatzResearch.WordTrace]
  refine ⟨17962731877782086701313809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23950309170376115601751745 17962731877782086701313809)
  ·
    refine ⟨13472048908336565025985357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17962731877782086701313809 13472048908336565025985357)
    ·
      refine ⟨5052018340626211884744509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13472048908336565025985357 5052018340626211884744509)
      ·
        refine ⟨1894506877734829456779191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5052018340626211884744509 1894506877734829456779191)
        ·
          refine ⟨2841760316602244185168787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894506877734829456779191 2841760316602244185168787)
          ·
            refine ⟨4262640474903366277753181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841760316602244185168787 4262640474903366277753181)
            ·
              refine ⟨1598490178088762354157443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4262640474903366277753181 1598490178088762354157443)
              ·
                refine ⟨2397735267133143531236165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598490178088762354157443 2397735267133143531236165)
                ·
                  refine ⟨449575362587464412106781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397735267133143531236165 449575362587464412106781)
                  ·
                    rfl

theorem cell20_984988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_984988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_984988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_984988 prefixEnd_984988 := by exact prefixLift 984988
  have htrace : WordTrace (prefixWord ++ tailWord_984988) baseStart_984988 baseEnd_984988 := by
    simpa [prefixWord, tailWord_984988, baseEnd_984988] using wordTrace_append hprefix tailTrace_984988
  have hstable : (prefixWord ++ tailWord_984988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984988).length < 2 ^ (prefixWord ++ tailWord_984988).sum := by decide
  have hdescent : baseEnd_984988 < baseStart_984988 := by decide
  rcases family_descends (prefixWord ++ tailWord_984988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985050 : List Nat := [3, 1, 1, 2, 6, 1, 1, 5]
def baseStart_985050 : Nat := 118140960795 + 985050 * 2 ^ 59
def prefixEnd_985050 : Nat := 4983230072969 + 3 ^ 40 * 985050 * 2
def baseEnd_985050 : Nat := 149867887025622584013287

theorem tailTrace_985050 : CollatzResearch.WordTrace tailWord_985050 prefixEnd_985050 149867887025622584013287 := by
  unfold tailWord_985050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8981931270334889497846151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23951816720893038660923069 8981931270334889497846151)
  ·
    refine ⟨13472896905502334246769227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8981931270334889497846151 13472896905502334246769227)
    ·
      refine ⟨20209345358253501370153841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13472896905502334246769227 20209345358253501370153841)
      ·
        refine ⟨15157009018690126027615381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20209345358253501370153841 15157009018690126027615381)
        ·
          refine ⟨710484797751099657544471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15157009018690126027615381 710484797751099657544471)
          ·
            refine ⟨1065727196626649486316707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710484797751099657544471 1065727196626649486316707)
            ·
              refine ⟨1598590794939974229475061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065727196626649486316707 1598590794939974229475061)
              ·
                refine ⟨149867887025622584013287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1598590794939974229475061 149867887025622584013287)
                ·
                  rfl

theorem cell20_985050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_985050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985050 prefixEnd_985050 := by exact prefixLift 985050
  have htrace : WordTrace (prefixWord ++ tailWord_985050) baseStart_985050 baseEnd_985050 := by
    simpa [prefixWord, tailWord_985050, baseEnd_985050] using wordTrace_append hprefix tailTrace_985050
  have hstable : (prefixWord ++ tailWord_985050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985050).length < 2 ^ (prefixWord ++ tailWord_985050).sum := by decide
  have hdescent : baseEnd_985050 < baseStart_985050 := by decide
  rcases family_descends (prefixWord ++ tailWord_985050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985075 : List Nat := [1, 1, 1, 2, 2, 2, 1, 10]
def baseStart_985075 : Nat := 118140960795 + 985075 * 2 ^ 59
def prefixEnd_985075 : Nat := 4983230072969 + 3 ^ 40 * 985075 * 2
def baseEnd_985075 : Nat := 149871690586026258735475

theorem tailTrace_985075 : CollatzResearch.WordTrace tailWord_985075 prefixEnd_985075 149871690586026258735475 := by
  unfold tailWord_985075
  simp only [CollatzResearch.WordTrace]
  refine ⟨35928636906248987261044679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23952424604165991507363119 35928636906248987261044679)
  ·
    refine ⟨53892955359373480891567019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35928636906248987261044679 53892955359373480891567019)
    ·
      refine ⟨80839433039060221337350529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53892955359373480891567019 80839433039060221337350529)
      ·
        refine ⟨60629574779295166003012897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80839433039060221337350529 60629574779295166003012897)
        ·
          refine ⟨45472181084471374502259673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60629574779295166003012897 45472181084471374502259673)
          ·
            refine ⟨34104135813353530876694755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45472181084471374502259673 34104135813353530876694755)
            ·
              refine ⟨51156203720030296315042133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34104135813353530876694755 51156203720030296315042133)
              ·
                refine ⟨149871690586026258735475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51156203720030296315042133 149871690586026258735475)
                ·
                  rfl

theorem cell20_985075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_985075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985075 prefixEnd_985075 := by exact prefixLift 985075
  have htrace : WordTrace (prefixWord ++ tailWord_985075) baseStart_985075 baseEnd_985075 := by
    simpa [prefixWord, tailWord_985075, baseEnd_985075] using wordTrace_append hprefix tailTrace_985075
  have hstable : (prefixWord ++ tailWord_985075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985075).length < 2 ^ (prefixWord ++ tailWord_985075).sum := by decide
  have hdescent : baseEnd_985075 < baseStart_985075 := by decide
  rcases family_descends (prefixWord ++ tailWord_985075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985095 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 3]
def baseStart_985095 : Nat := 118140960795 + 985095 * 2 ^ 59
def prefixEnd_985095 : Nat := 4983230072969 + 3 ^ 40 * 985095 * 2
def baseEnd_985095 : Nat := 449624200303047595539677

theorem tailTrace_985095 : CollatzResearch.WordTrace tailWord_985095 prefixEnd_985095 449624200303047595539677 := by
  unfold tailWord_985095
  simp only [CollatzResearch.WordTrace]
  refine ⟨35929366366176530676772739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23952910910784353784515159 35929366366176530676772739)
  ·
    refine ⟨53894049549264796015159109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35929366366176530676772739 53894049549264796015159109)
    ·
      refine ⟨10105134290487149252842333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53894049549264796015159109 10105134290487149252842333)
      ·
        refine ⟨3789425358932680969815875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10105134290487149252842333 3789425358932680969815875)
        ·
          refine ⟨5684138038399021454723813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3789425358932680969815875 5684138038399021454723813)
          ·
            refine ⟨1065775882199816522760715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5684138038399021454723813 1065775882199816522760715)
            ·
              refine ⟨1598663823299724784141073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065775882199816522760715 1598663823299724784141073)
              ·
                refine ⟨1198997867474793588105805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1598663823299724784141073 1198997867474793588105805)
                ·
                  refine ⟨449624200303047595539677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198997867474793588105805 449624200303047595539677)
                  ·
                    rfl

theorem cell20_985095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 3].length) (baseStart_985095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985095 prefixEnd_985095 := by exact prefixLift 985095
  have htrace : WordTrace (prefixWord ++ tailWord_985095) baseStart_985095 baseEnd_985095 := by
    simpa [prefixWord, tailWord_985095, baseEnd_985095] using wordTrace_append hprefix tailTrace_985095
  have hstable : (prefixWord ++ tailWord_985095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985095).length < 2 ^ (prefixWord ++ tailWord_985095).sum := by decide
  have hdescent : baseEnd_985095 < baseStart_985095 := by decide
  rcases family_descends (prefixWord ++ tailWord_985095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985099 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_985099 : Nat := 118140960795 + 985099 * 2 ^ 59
def prefixEnd_985099 : Nat := 4983230072969 + 3 ^ 40 * 985099 * 2
def baseEnd_985099 : Nat := 449626026012041359406327

theorem tailTrace_985099 : CollatzResearch.WordTrace tailWord_985099 prefixEnd_985099 449626026012041359406327 := by
  unfold tailWord_985099
  simp only [CollatzResearch.WordTrace]
  refine ⟨35929512258162039359918351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23953008172108026239945567 35929512258162039359918351)
  ·
    refine ⟨53894268387243059039877527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35929512258162039359918351 53894268387243059039877527)
    ·
      refine ⟨80841402580864588559816291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53894268387243059039877527 80841402580864588559816291)
      ·
        refine ⟨121262103871296882839724437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80841402580864588559816291 121262103871296882839724437)
        ·
          refine ⟨5684161118967041383112083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121262103871296882839724437 5684161118967041383112083)
          ·
            refine ⟨8526241678450562074668125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5684161118967041383112083 8526241678450562074668125)
            ·
              refine ⟨3197340629418960778000547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8526241678450562074668125 3197340629418960778000547)
              ·
                refine ⟨4796010944128441167000821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197340629418960778000547 4796010944128441167000821)
                ·
                  refine ⟨449626026012041359406327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4796010944128441167000821 449626026012041359406327)
                  ·
                    rfl

theorem cell20_985099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_985099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985099 prefixEnd_985099 := by exact prefixLift 985099
  have htrace : WordTrace (prefixWord ++ tailWord_985099) baseStart_985099 baseEnd_985099 := by
    simpa [prefixWord, tailWord_985099, baseEnd_985099] using wordTrace_append hprefix tailTrace_985099
  have hstable : (prefixWord ++ tailWord_985099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985099).length < 2 ^ (prefixWord ++ tailWord_985099).sum := by decide
  have hdescent : baseEnd_985099 < baseStart_985099 := by decide
  rcases family_descends (prefixWord ++ tailWord_985099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985102 : List Nat := [4, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_985102 : Nat := 118140960795 + 985102 * 2 ^ 59
def prefixEnd_985102 : Nat := 4983230072969 + 3 ^ 40 * 985102 * 2
def baseEnd_985102 : Nat := 449627395293786682306315

theorem tailTrace_985102 : CollatzResearch.WordTrace tailWord_985102 prefixEnd_985102 449627395293786682306315 := by
  unfold tailWord_985102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491202709643896359034695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23953081118100780581518373 4491202709643896359034695)
  ·
    refine ⟨6736804064465844538552043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4491202709643896359034695 6736804064465844538552043)
    ·
      refine ⟨10105206096698766807828065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6736804064465844538552043 10105206096698766807828065)
      ·
        refine ⟨7578904572524075105871049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10105206096698766807828065 7578904572524075105871049)
        ·
          refine ⟨5684178429393056329403287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7578904572524075105871049 5684178429393056329403287)
          ·
            refine ⟨8526267644089584494104931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5684178429393056329403287 8526267644089584494104931)
            ·
              refine ⟨12789401466134376741157397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8526267644089584494104931 12789401466134376741157397)
              ·
                refine ⟨599503193725048909741753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12789401466134376741157397 599503193725048909741753)
                ·
                  refine ⟨449627395293786682306315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599503193725048909741753 449627395293786682306315)
                  ·
                    rfl

theorem cell20_985102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_985102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985102 prefixEnd_985102 := by exact prefixLift 985102
  have htrace : WordTrace (prefixWord ++ tailWord_985102) baseStart_985102 baseEnd_985102 := by
    simpa [prefixWord, tailWord_985102, baseEnd_985102] using wordTrace_append hprefix tailTrace_985102
  have hstable : (prefixWord ++ tailWord_985102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985102).length < 2 ^ (prefixWord ++ tailWord_985102).sum := by decide
  have hdescent : baseEnd_985102 < baseStart_985102 := by decide
  rcases family_descends (prefixWord ++ tailWord_985102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985113 : List Nat := [1, 2, 1, 2, 1, 1, 3, 9]
def baseStart_985113 : Nat := 118140960795 + 985113 * 2 ^ 59
def prefixEnd_985113 : Nat := 4983230072969 + 3 ^ 40 * 985113 * 2
def baseEnd_985113 : Nat := 149877471997839844313201

theorem tailTrace_985113 : CollatzResearch.WordTrace tailWord_985113 prefixEnd_985113 149877471997839844313201 := by
  unfold tailWord_985113
  simp only [CollatzResearch.WordTrace]
  refine ⟨35930022880111319750927993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23953348586740879833951995 35930022880111319750927993)
  ·
    refine ⟨26947517160083489813195995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35930022880111319750927993 26947517160083489813195995)
    ·
      refine ⟨40421275740125234719793993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26947517160083489813195995 40421275740125234719793993)
      ·
        refine ⟨30315956805093926039845495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40421275740125234719793993 30315956805093926039845495)
        ·
          refine ⟨45473935207640889059768243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30315956805093926039845495 45473935207640889059768243)
          ·
            refine ⟨68210902811461333589652365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45473935207640889059768243 68210902811461333589652365)
            ·
              refine ⟨25579088554298000096119637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68210902811461333589652365 25579088554298000096119637)
              ·
                refine ⟨149877471997839844313201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25579088554298000096119637 149877471997839844313201)
                ·
                  rfl

theorem cell20_985113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_985113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985113 prefixEnd_985113 := by exact prefixLift 985113
  have htrace : WordTrace (prefixWord ++ tailWord_985113) baseStart_985113 baseEnd_985113 := by
    simpa [prefixWord, tailWord_985113, baseEnd_985113] using wordTrace_append hprefix tailTrace_985113
  have hstable : (prefixWord ++ tailWord_985113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985113).length < 2 ^ (prefixWord ++ tailWord_985113).sum := by decide
  have hdescent : baseEnd_985113 < baseStart_985113 := by decide
  rcases family_descends (prefixWord ++ tailWord_985113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985137 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_985137 : Nat := 118140960795 + 985137 * 2 ^ 59
def prefixEnd_985137 : Nat := 4983230072969 + 3 ^ 40 * 985137 * 2
def baseEnd_985137 : Nat := 449643370247482116139505

theorem tailTrace_985137 : CollatzResearch.WordTrace tailWord_985137 prefixEnd_985137 449643370247482116139505 := by
  unfold tailWord_985137
  simp only [CollatzResearch.WordTrace]
  refine ⟨35930898232024371849801665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23953932154682914566534443 35930898232024371849801665)
  ·
    refine ⟨26948173674018278887351249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35930898232024371849801665 26948173674018278887351249)
    ·
      refine ⟨20211130255513709165513437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26948173674018278887351249 20211130255513709165513437)
      ·
        refine ⟨7579173845817640937067539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20211130255513709165513437 7579173845817640937067539)
        ·
          refine ⟨11368760768726461405601309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7579173845817640937067539 11368760768726461405601309)
          ·
            refine ⟨4263285288272423027100491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11368760768726461405601309 4263285288272423027100491)
            ·
              refine ⟨6394927932408634540650737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4263285288272423027100491 6394927932408634540650737)
              ·
                refine ⟨4796195949306475905488053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6394927932408634540650737 4796195949306475905488053)
                ·
                  refine ⟨449643370247482116139505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4796195949306475905488053 449643370247482116139505)
                  ·
                    rfl

theorem cell20_985137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_985137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985137 prefixEnd_985137 := by exact prefixLift 985137
  have htrace : WordTrace (prefixWord ++ tailWord_985137) baseStart_985137 baseEnd_985137 := by
    simpa [prefixWord, tailWord_985137, baseEnd_985137] using wordTrace_append hprefix tailTrace_985137
  have hstable : (prefixWord ++ tailWord_985137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985137).length < 2 ^ (prefixWord ++ tailWord_985137).sum := by decide
  have hdescent : baseEnd_985137 < baseStart_985137 := by decide
  rcases family_descends (prefixWord ++ tailWord_985137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985151 : List Nat := [1, 1, 2, 2, 3, 1, 10]
def baseStart_985151 : Nat := 118140960795 + 985151 * 2 ^ 59
def prefixEnd_985151 : Nat := 4983230072969 + 3 ^ 40 * 985151 * 2
def baseEnd_985151 : Nat := 49961084469884476630309

theorem tailTrace_985151 : CollatzResearch.WordTrace tailWord_985151 prefixEnd_985151 49961084469884476630309 := by
  unfold tailWord_985151
  simp only [CollatzResearch.WordTrace]
  refine ⟨35931408853973652240811307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23954272569315768160540871 35931408853973652240811307)
  ·
    refine ⟨53897113280960478361216961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35931408853973652240811307 53897113280960478361216961)
    ·
      refine ⟨40422834960720358770912721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53897113280960478361216961 40422834960720358770912721)
      ·
        refine ⟨30317126220540269078184541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40422834960720358770912721 30317126220540269078184541)
        ·
          refine ⟨11368922332702600904319203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30317126220540269078184541 11368922332702600904319203)
          ·
            refine ⟨17053383499053901356478805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11368922332702600904319203 17053383499053901356478805)
            ·
              refine ⟨49961084469884476630309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17053383499053901356478805 49961084469884476630309)
              ·
                rfl

theorem cell20_985151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 10].length) (baseStart_985151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985151 prefixEnd_985151 := by exact prefixLift 985151
  have htrace : WordTrace (prefixWord ++ tailWord_985151) baseStart_985151 baseEnd_985151 := by
    simpa [prefixWord, tailWord_985151, baseEnd_985151] using wordTrace_append hprefix tailTrace_985151
  have hstable : (prefixWord ++ tailWord_985151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985151).length < 2 ^ (prefixWord ++ tailWord_985151).sum := by decide
  have hdescent : baseEnd_985151 < baseStart_985151 := by decide
  rcases family_descends (prefixWord ++ tailWord_985151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985206 : List Nat := [5, 1, 1, 2, 1, 10]
def baseStart_985206 : Nat := 118140960795 + 985206 * 2 ^ 59
def prefixEnd_985206 : Nat := 4983230072969 + 3 ^ 40 * 985206 * 2
def baseEnd_985206 : Nat := 16654624582504612697749

theorem tailTrace_985206 : CollatzResearch.WordTrace tailWord_985206 prefixEnd_985206 16654624582504612697749 := by
  unfold tailWord_985206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245838429298399789628967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23955609912516264422708981 2245838429298399789628967)
  ·
    refine ⟨3368757643947599684443451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2245838429298399789628967 3368757643947599684443451)
    ·
      refine ⟨5053136465921399526665177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3368757643947599684443451 5053136465921399526665177)
      ·
        refine ⟨3789852349441049644998883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5053136465921399526665177 3789852349441049644998883)
        ·
          refine ⟨5684778524161574467498325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3789852349441049644998883 5684778524161574467498325)
          ·
            refine ⟨16654624582504612697749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5684778524161574467498325 16654624582504612697749)
            ·
              rfl

theorem cell20_985206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 10].length) (baseStart_985206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985206 prefixEnd_985206 := by exact prefixLift 985206
  have htrace : WordTrace (prefixWord ++ tailWord_985206) baseStart_985206 baseEnd_985206 := by
    simpa [prefixWord, tailWord_985206, baseEnd_985206] using wordTrace_append hprefix tailTrace_985206
  have hstable : (prefixWord ++ tailWord_985206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985206).length < 2 ^ (prefixWord ++ tailWord_985206).sum := by decide
  have hdescent : baseEnd_985206 < baseStart_985206 := by decide
  rcases family_descends (prefixWord ++ tailWord_985206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985275 : List Nat := [1, 1, 1, 1, 1, 2, 5, 6, 2]
def baseStart_985275 : Nat := 118140960795 + 985275 * 2 ^ 59
def prefixEnd_985275 : Nat := 4983230072969 + 3 ^ 40 * 985275 * 2
def baseEnd_985275 : Nat := 449706357207766969538941

theorem tailTrace_985275 : CollatzResearch.WordTrace tailWord_985275 prefixEnd_985275 449706357207766969538941 := by
  unfold tailWord_985275
  simp only [CollatzResearch.WordTrace]
  refine ⟨35935931505524421418325279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23957287670349614278883519 35935931505524421418325279)
  ·
    refine ⟨53903897258286632127487919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35935931505524421418325279 53903897258286632127487919)
    ·
      refine ⟨80855845887429948191231879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53903897258286632127487919 80855845887429948191231879)
      ·
        refine ⟨121283768831144922286847819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80855845887429948191231879 121283768831144922286847819)
        ·
          refine ⟨181925653246717383430271729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121283768831144922286847819 181925653246717383430271729)
          ·
            refine ⟨136444239935038037572703797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181925653246717383430271729 136444239935038037572703797)
            ·
              refine ⟨12791647493909816022440981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136444239935038037572703797 12791647493909816022440981)
              ·
                refine ⟨599608476277022626051921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12791647493909816022440981 599608476277022626051921)
                ·
                  refine ⟨449706357207766969538941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599608476277022626051921 449706357207766969538941)
                  ·
                    rfl

theorem cell20_985275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 2].length) (baseStart_985275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985275 prefixEnd_985275 := by exact prefixLift 985275
  have htrace : WordTrace (prefixWord ++ tailWord_985275) baseStart_985275 baseEnd_985275 := by
    simpa [prefixWord, tailWord_985275, baseEnd_985275] using wordTrace_append hprefix tailTrace_985275
  have hstable : (prefixWord ++ tailWord_985275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985275).length < 2 ^ (prefixWord ++ tailWord_985275).sum := by decide
  have hdescent : baseEnd_985275 < baseStart_985275 := by decide
  rcases family_descends (prefixWord ++ tailWord_985275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985309 : List Nat := [1, 4, 3, 2, 1, 1, 3, 3, 2]
def baseStart_985309 : Nat := 118140960795 + 985309 * 2 ^ 59
def prefixEnd_985309 : Nat := 4983230072969 + 3 ^ 40 * 985309 * 2
def baseEnd_985309 : Nat := 449721875734213962405469

theorem tailTrace_985309 : CollatzResearch.WordTrace tailWord_985309 prefixEnd_985309 449721875734213962405469 := by
  unfold tailWord_985309
  simp only [CollatzResearch.WordTrace]
  refine ⟨35937171587401245225062981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23958114391600830150041987 35937171587401245225062981)
  ·
    refine ⟨6738219672637733479699309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35937171587401245225062981 6738219672637733479699309)
    ·
      refine ⟨2526832377239150054887241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6738219672637733479699309 2526832377239150054887241)
      ·
        refine ⟨1895124282929362541165431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2526832377239150054887241 1895124282929362541165431)
        ·
          refine ⟨2842686424394043811748147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895124282929362541165431 2842686424394043811748147)
          ·
            refine ⟨4264029636591065717622221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842686424394043811748147 4264029636591065717622221)
            ·
              refine ⟨1599011113721649644108333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4264029636591065717622221 1599011113721649644108333)
              ·
                refine ⟨599629167645618616540625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1599011113721649644108333 599629167645618616540625)
                ·
                  refine ⟨449721875734213962405469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599629167645618616540625 449721875734213962405469)
                  ·
                    rfl

theorem cell20_985309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_985309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985309 prefixEnd_985309 := by exact prefixLift 985309
  have htrace : WordTrace (prefixWord ++ tailWord_985309) baseStart_985309 baseEnd_985309 := by
    simpa [prefixWord, tailWord_985309, baseEnd_985309] using wordTrace_append hprefix tailTrace_985309
  have hstable : (prefixWord ++ tailWord_985309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985309).length < 2 ^ (prefixWord ++ tailWord_985309).sum := by decide
  have hdescent : baseEnd_985309 < baseStart_985309 := by decide
  rcases family_descends (prefixWord ++ tailWord_985309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985320 : List Nat := [2, 1, 4, 1, 2, 4, 6]
def baseStart_985320 : Nat := 118140960795 + 985320 * 2 ^ 59
def prefixEnd_985320 : Nat := 4983230072969 + 3 ^ 40 * 985320 * 2
def baseEnd_985320 : Nat := 49969655159327423670973

theorem tailTrace_985320 : CollatzResearch.WordTrace tailWord_985320 prefixEnd_985320 49969655159327423670973 := by
  unfold tailWord_985320
  simp only [CollatzResearch.WordTrace]
  refine ⟨17968786395180697051856707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23958381860240929402475609 17968786395180697051856707)
  ·
    refine ⟨26953179592771045577785061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17968786395180697051856707 26953179592771045577785061)
    ·
      refine ⟨5053721173644571045834699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26953179592771045577785061 5053721173644571045834699)
      ·
        refine ⟨7580581760466856568752049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5053721173644571045834699 7580581760466856568752049)
        ·
          refine ⟨5685436320350142426564037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7580581760466856568752049 5685436320350142426564037)
          ·
            refine ⟨1066019310065651704980757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5685436320350142426564037 1066019310065651704980757)
            ·
              refine ⟨49969655159327423670973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1066019310065651704980757 49969655159327423670973)
              ·
                rfl

theorem cell20_985320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 6].length) (baseStart_985320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985320 prefixEnd_985320 := by exact prefixLift 985320
  have htrace : WordTrace (prefixWord ++ tailWord_985320) baseStart_985320 baseEnd_985320 := by
    simpa [prefixWord, tailWord_985320, baseEnd_985320] using wordTrace_append hprefix tailTrace_985320
  have hstable : (prefixWord ++ tailWord_985320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985320).length < 2 ^ (prefixWord ++ tailWord_985320).sum := by decide
  have hdescent : baseEnd_985320 < baseStart_985320 := by decide
  rcases family_descends (prefixWord ++ tailWord_985320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985327 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_985327 : Nat := 118140960795 + 985327 * 2 ^ 59
def prefixEnd_985327 : Nat := 4983230072969 + 3 ^ 40 * 985327 * 2
def baseEnd_985327 : Nat := 449730091424685899805395

theorem tailTrace_985327 : CollatzResearch.WordTrace tailWord_985327 prefixEnd_985327 449730091424685899805395 := by
  unfold tailWord_985327
  simp only [CollatzResearch.WordTrace]
  refine ⟨35937828101336034299218235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23958552067557356199478823 35937828101336034299218235)
  ·
    refine ⟨53906742152004051448827353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35937828101336034299218235 53906742152004051448827353)
    ·
      refine ⟨40430056614003038586620515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53906742152004051448827353 40430056614003038586620515)
      ·
        refine ⟨60645084921004557879930773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40430056614003038586620515 60645084921004557879930773)
        ·
          refine ⟨2842738355672088650621755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60645084921004557879930773 2842738355672088650621755)
          ·
            refine ⟨4264107533508132975932633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842738355672088650621755 4264107533508132975932633)
            ·
              refine ⟨3198080650131099731949475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264107533508132975932633 3198080650131099731949475)
              ·
                refine ⟨4797120975196649597924213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3198080650131099731949475 4797120975196649597924213)
                ·
                  refine ⟨449730091424685899805395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4797120975196649597924213 449730091424685899805395)
                  ·
                    rfl

theorem cell20_985327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_985327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985327 prefixEnd_985327 := by exact prefixLift 985327
  have htrace : WordTrace (prefixWord ++ tailWord_985327) baseStart_985327 baseEnd_985327 := by
    simpa [prefixWord, tailWord_985327, baseEnd_985327] using wordTrace_append hprefix tailTrace_985327
  have hstable : (prefixWord ++ tailWord_985327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985327).length < 2 ^ (prefixWord ++ tailWord_985327).sum := by decide
  have hdescent : baseEnd_985327 < baseStart_985327 := by decide
  rcases family_descends (prefixWord ++ tailWord_985327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985330 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_985330 : Nat := 118140960795 + 985330 * 2 ^ 59
def prefixEnd_985330 : Nat := 4983230072969 + 3 ^ 40 * 985330 * 2
def baseEnd_985330 : Nat := 449731460706431222705383

theorem tailTrace_985330 : CollatzResearch.WordTrace tailWord_985330 prefixEnd_985330 449731460706431222705383 := by
  unfold tailWord_985330
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984484380081291452894361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23958625013550110541051629 8984484380081291452894361)
  ·
    refine ⟨6738363285060968589670771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8984484380081291452894361 6738363285060968589670771)
    ·
      refine ⟨10107544927591452884506157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6738363285060968589670771 10107544927591452884506157)
      ·
        refine ⟨3790329347846794831689809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10107544927591452884506157 3790329347846794831689809)
        ·
          refine ⟨2842747010885096123767357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3790329347846794831689809 2842747010885096123767357)
          ·
            refine ⟨1066030129081911046412759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2842747010885096123767357 1066030129081911046412759)
            ·
              refine ⟨1599045193622866569619139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066030129081911046412759 1599045193622866569619139)
              ·
                refine ⟨2398567790434299854428709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599045193622866569619139 2398567790434299854428709)
                ·
                  refine ⟨449731460706431222705383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2398567790434299854428709 449731460706431222705383)
                  ·
                    rfl

theorem cell20_985330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_985330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985330 prefixEnd_985330 := by exact prefixLift 985330
  have htrace : WordTrace (prefixWord ++ tailWord_985330) baseStart_985330 baseEnd_985330 := by
    simpa [prefixWord, tailWord_985330, baseEnd_985330] using wordTrace_append hprefix tailTrace_985330
  have hstable : (prefixWord ++ tailWord_985330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985330).length < 2 ^ (prefixWord ++ tailWord_985330).sum := by decide
  have hdescent : baseEnd_985330 < baseStart_985330 := by decide
  rcases family_descends (prefixWord ++ tailWord_985330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985344 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 3]
def baseStart_985344 : Nat := 118140960795 + 985344 * 2 ^ 59
def prefixEnd_985344 : Nat := 4983230072969 + 3 ^ 40 * 985344 * 2
def baseEnd_985344 : Nat := 449737850687909396238659

theorem tailTrace_985344 : CollatzResearch.WordTrace tailWord_985344 prefixEnd_985344 449737850687909396238659 := by
  unfold tailWord_985344
  simp only [CollatzResearch.WordTrace]
  refine ⟨17969224071137223101293543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23958965428182964135058057 17969224071137223101293543)
  ·
    refine ⟨26953836106705834651940315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17969224071137223101293543 26953836106705834651940315)
    ·
      refine ⟨40430754160058751977910473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26953836106705834651940315 40430754160058751977910473)
      ·
        refine ⟨30323065620044063983432855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40430754160058751977910473 30323065620044063983432855)
        ·
          refine ⟨45484598430066095975149283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30323065620044063983432855 45484598430066095975149283)
          ·
            refine ⟨68226897645099143962723925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45484598430066095975149283 68226897645099143962723925)
            ·
              refine ⟨799533956778505593313171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 68226897645099143962723925 799533956778505593313171)
              ·
                refine ⟨1199300935167758389969757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799533956778505593313171 1199300935167758389969757)
                ·
                  refine ⟨449737850687909396238659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199300935167758389969757 449737850687909396238659)
                  ·
                    rfl

theorem cell20_985344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_985344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985344 prefixEnd_985344 := by exact prefixLift 985344
  have htrace : WordTrace (prefixWord ++ tailWord_985344) baseStart_985344 baseEnd_985344 := by
    simpa [prefixWord, tailWord_985344, baseEnd_985344] using wordTrace_append hprefix tailTrace_985344
  have hstable : (prefixWord ++ tailWord_985344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985344).length < 2 ^ (prefixWord ++ tailWord_985344).sum := by decide
  have hdescent : baseEnd_985344 < baseStart_985344 := by decide
  rcases family_descends (prefixWord ++ tailWord_985344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985548 : List Nat := [2, 2, 1, 4, 4, 7]
def baseStart_985548 : Nat := 118140960795 + 985548 * 2 ^ 59
def prefixEnd_985548 : Nat := 4983230072969 + 3 ^ 40 * 985548 * 2
def baseEnd_985548 : Nat := 16660405994318198275475

theorem tailTrace_985548 : CollatzResearch.WordTrace tailWord_985548 prefixEnd_985548 16660405994318198275475 := by
  unfold tailWord_985548
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972944316767694521506649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23963925755690259362008865 17972944316767694521506649)
  ·
    refine ⟨13479708237575770891129987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17972944316767694521506649 13479708237575770891129987)
    ·
      refine ⟨20219562356363656336694981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13479708237575770891129987 20219562356363656336694981)
      ·
        refine ⟨3791167941818185563130309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20219562356363656336694981 3791167941818185563130309)
        ·
          refine ⟨710843989090909793086933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3791167941818185563130309 710843989090909793086933)
          ·
            refine ⟨16660405994318198275475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 710843989090909793086933 16660405994318198275475)
            ·
              rfl

theorem cell20_985548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 7].length) (baseStart_985548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985548 prefixEnd_985548 := by exact prefixLift 985548
  have htrace : WordTrace (prefixWord ++ tailWord_985548) baseStart_985548 baseEnd_985548 := by
    simpa [prefixWord, tailWord_985548, baseEnd_985548] using wordTrace_append hprefix tailTrace_985548
  have hstable : (prefixWord ++ tailWord_985548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985548).length < 2 ^ (prefixWord ++ tailWord_985548).sum := by decide
  have hdescent : baseEnd_985548 < baseStart_985548 := by decide
  rcases family_descends (prefixWord ++ tailWord_985548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985562 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_985562 : Nat := 118140960795 + 985562 * 2 ^ 59
def prefixEnd_985562 : Nat := 4983230072969 + 3 ^ 40 * 985562 * 2
def baseEnd_985562 : Nat := 449837351828069526971101

theorem tailTrace_985562 : CollatzResearch.WordTrace tailWord_985562 prefixEnd_985562 449837351828069526971101 := by
  unfold tailWord_985562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8986599813871167358505735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23964266170323112956015293 8986599813871167358505735)
  ·
    refine ⟨13479899720806751037758603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8986599813871167358505735 13479899720806751037758603)
    ·
      refine ⟨20219849581210126556637905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13479899720806751037758603 20219849581210126556637905)
      ·
        refine ⟨15164887185907594917478429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20219849581210126556637905 15164887185907594917478429)
        ·
          refine ⟨5686832694715348094054411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15164887185907594917478429 5686832694715348094054411)
          ·
            refine ⟨8530249042073022141081617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686832694715348094054411 8530249042073022141081617)
            ·
              refine ⟨6397686781554766605811213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8530249042073022141081617 6397686781554766605811213)
              ·
                refine ⟨2399132543083037477179205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6397686781554766605811213 2399132543083037477179205)
                ·
                  refine ⟨449837351828069526971101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399132543083037477179205 449837351828069526971101)
                  ·
                    rfl

theorem cell20_985562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_985562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985562 prefixEnd_985562 := by exact prefixLift 985562
  have htrace : WordTrace (prefixWord ++ tailWord_985562) baseStart_985562 baseEnd_985562 := by
    simpa [prefixWord, tailWord_985562, baseEnd_985562] using wordTrace_append hprefix tailTrace_985562
  have hstable : (prefixWord ++ tailWord_985562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985562).length < 2 ^ (prefixWord ++ tailWord_985562).sum := by decide
  have hdescent : baseEnd_985562 < baseStart_985562 := by decide
  rcases family_descends (prefixWord ++ tailWord_985562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985606 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_985606 : Nat := 118140960795 + 985606 * 2 ^ 59
def prefixEnd_985606 : Nat := 4983230072969 + 3 ^ 40 * 985606 * 2
def baseEnd_985606 : Nat := 449857434627000929504255

theorem tailTrace_985606 : CollatzResearch.WordTrace tailWord_985606 prefixEnd_985606 449857434627000929504255 := by
  unfold tailWord_985606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1123375127103914529644521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23965336044883509965749781 1123375127103914529644521)
  ·
    refine ⟨842531345327935897233391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1123375127103914529644521 842531345327935897233391)
    ·
      refine ⟨1263797017991903845850087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842531345327935897233391 1263797017991903845850087)
      ·
        refine ⟨1895695526987855768775131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263797017991903845850087 1895695526987855768775131)
        ·
          refine ⟨2843543290481783653162697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895695526987855768775131 2843543290481783653162697)
          ·
            refine ⟨2132657467861337739872023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2843543290481783653162697 2132657467861337739872023)
            ·
              refine ⟨3198986201792006609808035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132657467861337739872023 3198986201792006609808035)
              ·
                refine ⟨4798479302688009914712053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3198986201792006609808035 4798479302688009914712053)
                ·
                  refine ⟨449857434627000929504255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4798479302688009914712053 449857434627000929504255)
                  ·
                    rfl

theorem cell20_985606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_985606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985606 prefixEnd_985606 := by exact prefixLift 985606
  have htrace : WordTrace (prefixWord ++ tailWord_985606) baseStart_985606 baseEnd_985606 := by
    simpa [prefixWord, tailWord_985606, baseEnd_985606] using wordTrace_append hprefix tailTrace_985606
  have hstable : (prefixWord ++ tailWord_985606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985606).length < 2 ^ (prefixWord ++ tailWord_985606).sum := by decide
  have hdescent : baseEnd_985606 < baseStart_985606 := by decide
  rcases family_descends (prefixWord ++ tailWord_985606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985613 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 4]
def baseStart_985613 : Nat := 118140960795 + 985613 * 2 ^ 59
def prefixEnd_985613 : Nat := 4983230072969 + 3 ^ 40 * 985613 * 2
def baseEnd_985613 : Nat := 449860629617740016270893

theorem tailTrace_985613 : CollatzResearch.WordTrace tailWord_985613 prefixEnd_985613 449860629617740016270893 := by
  unfold tailWord_985613
  simp only [CollatzResearch.WordTrace]
  refine ⟨35948259378299905144129493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23965506252199936762752995 35948259378299905144129493)
  ·
    refine ⟨842537329178904026815535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35948259378299905144129493 842537329178904026815535)
    ·
      refine ⟨1263805993768356040223303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842537329178904026815535 1263805993768356040223303)
      ·
        refine ⟨1895708990652534060334955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263805993768356040223303 1895708990652534060334955)
        ·
          refine ⟨2843563485978801090502433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895708990652534060334955 2843563485978801090502433)
          ·
            refine ⟨2132672614484100817876825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2843563485978801090502433 2132672614484100817876825)
            ·
              refine ⟨1599504460863075613407619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2132672614484100817876825 1599504460863075613407619)
              ·
                refine ⟨2399256691294613420111429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599504460863075613407619 2399256691294613420111429)
                ·
                  refine ⟨449860629617740016270893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399256691294613420111429 449860629617740016270893)
                  ·
                    rfl

theorem cell20_985613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_985613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985613 prefixEnd_985613 := by exact prefixLift 985613
  have htrace : WordTrace (prefixWord ++ tailWord_985613) baseStart_985613 baseEnd_985613 := by
    simpa [prefixWord, tailWord_985613, baseEnd_985613] using wordTrace_append hprefix tailTrace_985613
  have hstable : (prefixWord ++ tailWord_985613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985613).length < 2 ^ (prefixWord ++ tailWord_985613).sum := by decide
  have hdescent : baseEnd_985613 < baseStart_985613 := by decide
  rcases family_descends (prefixWord ++ tailWord_985613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985668 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 4]
def baseStart_985668 : Nat := 118140960795 + 985668 * 2 ^ 59
def prefixEnd_985668 : Nat := 4983230072969 + 3 ^ 40 * 985668 * 2
def baseEnd_985668 : Nat := 449885733116404269437335

theorem tailTrace_985668 : CollatzResearch.WordTrace tailWord_985668 prefixEnd_985668 449885733116404269437335 := by
  unfold tailWord_985668
  simp only [CollatzResearch.WordTrace]
  refine ⟨17975132696550324768690829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23966843595400433024921105 17975132696550324768690829)
  ·
    refine ⟨6740674761206371788259061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17975132696550324768690829 6740674761206371788259061)
    ·
      refine ⟨631938258863097355149287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6740674761206371788259061 631938258863097355149287)
      ·
        refine ⟨947907388294646032723931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631938258863097355149287 947907388294646032723931)
        ·
          refine ⟨1421861082441969049085897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947907388294646032723931 1421861082441969049085897)
          ·
            refine ⟨1066395811831476786814423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421861082441969049085897 1066395811831476786814423)
            ·
              refine ⟨1599593717747215180221635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066395811831476786814423 1599593717747215180221635)
              ·
                refine ⟨2399390576620822770332453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599593717747215180221635 2399390576620822770332453)
                ·
                  refine ⟨449885733116404269437335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399390576620822770332453 449885733116404269437335)
                  ·
                    rfl

theorem cell20_985668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_985668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985668 prefixEnd_985668 := by exact prefixLift 985668
  have htrace : WordTrace (prefixWord ++ tailWord_985668) baseStart_985668 baseEnd_985668 := by
    simpa [prefixWord, tailWord_985668, baseEnd_985668] using wordTrace_append hprefix tailTrace_985668
  have hstable : (prefixWord ++ tailWord_985668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985668).length < 2 ^ (prefixWord ++ tailWord_985668).sum := by decide
  have hdescent : baseEnd_985668 < baseStart_985668 := by decide
  rcases family_descends (prefixWord ++ tailWord_985668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985730 : List Nat := [3, 4, 3, 1, 2, 1, 1, 5]
def baseStart_985730 : Nat := 118140960795 + 985730 * 2 ^ 59
def prefixEnd_985730 : Nat := 4983230072969 + 3 ^ 40 * 985730 * 2
def baseEnd_985730 : Nat := 149971343868602536456805

theorem tailTrace_985730 : CollatzResearch.WordTrace tailWord_985730 prefixEnd_985730 149971343868602536456805 := by
  unfold tailWord_985730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988131679719008531534661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23968351145917356084092429 8988131679719008531534661)
  ·
    refine ⟨1685274689947314099662749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8988131679719008531534661 1685274689947314099662749)
    ·
      refine ⟨631978008730242787373531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1685274689947314099662749 631978008730242787373531)
      ·
        refine ⟨947967013095364181060297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631978008730242787373531 947967013095364181060297)
        ·
          refine ⟨710975259821523135795223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 947967013095364181060297 710975259821523135795223)
          ·
            refine ⟨1066462889732284703692835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710975259821523135795223 1066462889732284703692835)
            ·
              refine ⟨1599694334598427055539253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066462889732284703692835 1599694334598427055539253)
              ·
                refine ⟨149971343868602536456805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1599694334598427055539253 149971343868602536456805)
                ·
                  rfl

theorem cell20_985730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_985730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985730 prefixEnd_985730 := by exact prefixLift 985730
  have htrace : WordTrace (prefixWord ++ tailWord_985730) baseStart_985730 baseEnd_985730 := by
    simpa [prefixWord, tailWord_985730, baseEnd_985730] using wordTrace_append hprefix tailTrace_985730
  have hstable : (prefixWord ++ tailWord_985730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985730).length < 2 ^ (prefixWord ++ tailWord_985730).sum := by decide
  have hdescent : baseEnd_985730 < baseStart_985730 := by decide
  rcases family_descends (prefixWord ++ tailWord_985730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985752 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_985752 : Nat := 118140960795 + 985752 * 2 ^ 59
def prefixEnd_985752 : Nat := 4983230072969 + 3 ^ 40 * 985752 * 2
def baseEnd_985752 : Nat := 449924073005273310636991

theorem tailTrace_985752 : CollatzResearch.WordTrace tailWord_985752 prefixEnd_985752 449924073005273310636991 := by
  unfold tailWord_985752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17976664562398165941719755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23968886083197554588959673 17976664562398165941719755)
  ·
    refine ⟨26964996843597248912579633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17976664562398165941719755 26964996843597248912579633)
    ·
      refine ⟨20223747632697936684434725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26964996843597248912579633 20223747632697936684434725)
      ·
        refine ⟨3791952681130863128331511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20223747632697936684434725 3791952681130863128331511)
        ·
          refine ⟨5687929021696294692497267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791952681130863128331511 5687929021696294692497267)
          ·
            refine ⟨8531893532544442038745901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5687929021696294692497267 8531893532544442038745901)
            ·
              refine ⟨3199460074704165764529713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8531893532544442038745901 3199460074704165764529713)
              ·
                refine ⟨2399595056028124323397285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3199460074704165764529713 2399595056028124323397285)
                ·
                  refine ⟨449924073005273310636991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399595056028124323397285 449924073005273310636991)
                  ·
                    rfl

theorem cell20_985752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_985752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985752 prefixEnd_985752 := by exact prefixLift 985752
  have htrace : WordTrace (prefixWord ++ tailWord_985752) baseStart_985752 baseEnd_985752 := by
    simpa [prefixWord, tailWord_985752, baseEnd_985752] using wordTrace_append hprefix tailTrace_985752
  have hstable : (prefixWord ++ tailWord_985752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985752).length < 2 ^ (prefixWord ++ tailWord_985752).sum := by decide
  have hdescent : baseEnd_985752 < baseStart_985752 := by decide
  rcases family_descends (prefixWord ++ tailWord_985752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985783 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 5]
def baseStart_985783 : Nat := 118140960795 + 985783 * 2 ^ 59
def prefixEnd_985783 : Nat := 4983230072969 + 3 ^ 40 * 985783 * 2
def baseEnd_985783 : Nat := 449938222249974980603531

theorem tailTrace_985783 : CollatzResearch.WordTrace tailWord_985783 prefixEnd_985783 449938222249974980603531 := by
  unfold tailWord_985783
  simp only [CollatzResearch.WordTrace]
  refine ⟨35954459787684024177818003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23969639858456016118545335 35954459787684024177818003)
  ·
    refine ⟨53931689681526036266727005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35954459787684024177818003 53931689681526036266727005)
    ·
      refine ⟨20224383630572263600022627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53931689681526036266727005 20224383630572263600022627)
      ·
        refine ⟨30336575445858395400033941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20224383630572263600022627 30336575445858395400033941)
        ·
          refine ⟨1422026974024612284376591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30336575445858395400033941 1422026974024612284376591)
          ·
            refine ⟨2133040461036918426564887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422026974024612284376591 2133040461036918426564887)
            ·
              refine ⟨3199560691555377639847331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133040461036918426564887 3199560691555377639847331)
              ·
                refine ⟨4799341037333066459770997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199560691555377639847331 4799341037333066459770997)
                ·
                  refine ⟨449938222249974980603531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4799341037333066459770997 449938222249974980603531)
                  ·
                    rfl

theorem cell20_985783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 5].length) (baseStart_985783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985783 prefixEnd_985783 := by exact prefixLift 985783
  have htrace : WordTrace (prefixWord ++ tailWord_985783) baseStart_985783 baseEnd_985783 := by
    simpa [prefixWord, tailWord_985783, baseEnd_985783] using wordTrace_append hprefix tailTrace_985783
  have hstable : (prefixWord ++ tailWord_985783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985783).length < 2 ^ (prefixWord ++ tailWord_985783).sum := by decide
  have hdescent : baseEnd_985783 < baseStart_985783 := by decide
  rcases family_descends (prefixWord ++ tailWord_985783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985800 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 3]
def baseStart_985800 : Nat := 118140960795 + 985800 * 2 ^ 59
def prefixEnd_985800 : Nat := 4983230072969 + 3 ^ 40 * 985800 * 2
def baseEnd_985800 : Nat := 449945981513198477036795

theorem tailTrace_985800 : CollatzResearch.WordTrace tailWord_985800 prefixEnd_985800 449945981513198477036795 := by
  unfold tailWord_985800
  simp only [CollatzResearch.WordTrace]
  refine ⟨17977539914311218040593427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23970053219081624054124569 17977539914311218040593427)
  ·
    refine ⟨26966309871466827060890141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17977539914311218040593427 26966309871466827060890141)
    ·
      refine ⟨10112366201800060147833803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26966309871466827060890141 10112366201800060147833803)
      ·
        refine ⟨15168549302700090221750705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10112366201800060147833803 15168549302700090221750705)
        ·
          refine ⟨11376411977025067666313029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15168549302700090221750705 11376411977025067666313029)
          ·
            refine ⟨2133077245692200187433693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11376411977025067666313029 2133077245692200187433693)
            ·
              refine ⟨799903967134575070287635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2133077245692200187433693 799903967134575070287635)
              ·
                refine ⟨1199855950701862605431453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799903967134575070287635 1199855950701862605431453)
                ·
                  refine ⟨449945981513198477036795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199855950701862605431453 449945981513198477036795)
                  ·
                    rfl

theorem cell20_985800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_985800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985800 prefixEnd_985800 := by exact prefixLift 985800
  have htrace : WordTrace (prefixWord ++ tailWord_985800) baseStart_985800 baseEnd_985800 := by
    simpa [prefixWord, tailWord_985800, baseEnd_985800] using wordTrace_append hprefix tailTrace_985800
  have hstable : (prefixWord ++ tailWord_985800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985800).length < 2 ^ (prefixWord ++ tailWord_985800).sum := by decide
  have hdescent : baseEnd_985800 < baseStart_985800 := by decide
  rcases family_descends (prefixWord ++ tailWord_985800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985810 : List Nat := [3, 2, 2, 2, 4, 1, 2, 4]
def baseStart_985810 : Nat := 118140960795 + 985810 * 2 ^ 59
def prefixEnd_985810 : Nat := 4983230072969 + 3 ^ 40 * 985810 * 2
def baseEnd_985810 : Nat := 149983515261894295567807

theorem tailTrace_985810 : CollatzResearch.WordTrace tailWord_985810 prefixEnd_985810 149983515261894295567807 := by
  unfold tailWord_985810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988861139646551947262721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23970296372390805192700589 8988861139646551947262721)
  ·
    refine ⟨6741645854734913960447041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8988861139646551947262721 6741645854734913960447041)
    ·
      refine ⟨5056234391051185470335281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6741645854734913960447041 5056234391051185470335281)
      ·
        refine ⟨3792175793288389102751461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5056234391051185470335281 3792175793288389102751461)
        ·
          refine ⟨711032961241572956765899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3792175793288389102751461 711032961241572956765899)
          ·
            refine ⟨1066549441862359435148849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711032961241572956765899 1066549441862359435148849)
            ·
              refine ⟨799912081396769576361637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066549441862359435148849 799912081396769576361637)
              ·
                refine ⟨149983515261894295567807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799912081396769576361637 149983515261894295567807)
                ·
                  rfl

theorem cell20_985810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_985810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985810 prefixEnd_985810 := by exact prefixLift 985810
  have htrace : WordTrace (prefixWord ++ tailWord_985810) baseStart_985810 baseEnd_985810 := by
    simpa [prefixWord, tailWord_985810, baseEnd_985810] using wordTrace_append hprefix tailTrace_985810
  have hstable : (prefixWord ++ tailWord_985810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985810).length < 2 ^ (prefixWord ++ tailWord_985810).sum := by decide
  have hdescent : baseEnd_985810 < baseStart_985810 := by decide
  rcases family_descends (prefixWord ++ tailWord_985810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985924 : List Nat := [2, 3, 4, 2, 1, 1, 3, 4]
def baseStart_985924 : Nat := 118140960795 + 985924 * 2 ^ 59
def prefixEnd_985924 : Nat := 4983230072969 + 3 ^ 40 * 985924 * 2
def baseEnd_985924 : Nat := 150000859497335052300985

theorem tailTrace_985924 : CollatzResearch.WordTrace tailWord_985924 prefixEnd_985924 150000859497335052300985 := by
  unfold tailWord_985924
  simp only [CollatzResearch.WordTrace]
  refine ⟨17979801240086602629350413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23973068320115470172467217 17979801240086602629350413)
  ·
    refine ⟨6742425465032475986006405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17979801240086602629350413 6742425465032475986006405)
    ·
      refine ⟨1264204774693589247376201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6742425465032475986006405 1264204774693589247376201)
      ·
        refine ⟨948153581020191935532151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1264204774693589247376201 948153581020191935532151)
        ·
          refine ⟨1422230371530287903298227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948153581020191935532151 1422230371530287903298227)
          ·
            refine ⟨2133345557295431854947341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422230371530287903298227 2133345557295431854947341)
            ·
              refine ⟨800004583985786945605253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2133345557295431854947341 800004583985786945605253)
              ·
                refine ⟨150000859497335052300985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 800004583985786945605253 150000859497335052300985)
                ·
                  rfl

theorem cell20_985924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_985924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985924 prefixEnd_985924 := by exact prefixLift 985924
  have htrace : WordTrace (prefixWord ++ tailWord_985924) baseStart_985924 baseEnd_985924 := by
    simpa [prefixWord, tailWord_985924, baseEnd_985924] using wordTrace_append hprefix tailTrace_985924
  have hstable : (prefixWord ++ tailWord_985924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985924).length < 2 ^ (prefixWord ++ tailWord_985924).sum := by decide
  have hdescent : baseEnd_985924 < baseStart_985924 := by decide
  rcases family_descends (prefixWord ++ tailWord_985924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985959 : List Nat := [1, 1, 5, 1, 2, 2, 2, 4, 2]
def baseStart_985959 : Nat := 118140960795 + 985959 * 2 ^ 59
def prefixEnd_985959 : Nat := 4983230072969 + 3 ^ 40 * 985959 * 2
def baseEnd_985959 : Nat := 450018553445700590736145

theorem tailTrace_985959 : CollatzResearch.WordTrace tailWord_985959 prefixEnd_985959 450018553445700590736145 := by
  unfold tailWord_985959
  simp only [CollatzResearch.WordTrace]
  refine ⟨35960879035046406236224931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23973919356697604157483287 35960879035046406236224931)
  ·
    refine ⟨53941318552569609354337397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35960879035046406236224931 53941318552569609354337397)
    ·
      refine ⟨5056998614303400876969131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53941318552569609354337397 5056998614303400876969131)
      ·
        refine ⟨7585497921455101315453697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5056998614303400876969131 7585497921455101315453697)
        ·
          refine ⟨5689123441091325986590273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7585497921455101315453697 5689123441091325986590273)
          ·
            refine ⟨4266842580818494489942705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5689123441091325986590273 4266842580818494489942705)
            ·
              refine ⟨3200131935613870867457029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4266842580818494489942705 3200131935613870867457029)
              ·
                refine ⟨600024737927600787648193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3200131935613870867457029 600024737927600787648193)
                ·
                  refine ⟨450018553445700590736145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600024737927600787648193 450018553445700590736145)
                  ·
                    rfl

theorem cell20_985959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 2].length) (baseStart_985959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985959 prefixEnd_985959 := by exact prefixLift 985959
  have htrace : WordTrace (prefixWord ++ tailWord_985959) baseStart_985959 baseEnd_985959 := by
    simpa [prefixWord, tailWord_985959, baseEnd_985959] using wordTrace_append hprefix tailTrace_985959
  have hstable : (prefixWord ++ tailWord_985959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985959).length < 2 ^ (prefixWord ++ tailWord_985959).sum := by decide
  have hdescent : baseEnd_985959 < baseStart_985959 := by decide
  rcases family_descends (prefixWord ++ tailWord_985959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985963 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_985963 : Nat := 118140960795 + 985963 * 2 ^ 59
def prefixEnd_985963 : Nat := 4983230072969 + 3 ^ 40 * 985963 * 2
def baseEnd_985963 : Nat := 450020379154694354602795

theorem tailTrace_985963 : CollatzResearch.WordTrace tailWord_985963 prefixEnd_985963 450020379154694354602795 := by
  unfold tailWord_985963
  simp only [CollatzResearch.WordTrace]
  refine ⟨35961024927031914919370543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23974016618021276612913695 35961024927031914919370543)
  ·
    refine ⟨53941537390547872379055815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35961024927031914919370543 53941537390547872379055815)
    ·
      refine ⟨80912306085821808568583723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53941537390547872379055815 80912306085821808568583723)
      ·
        refine ⟨121368459128732712852875585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80912306085821808568583723 121368459128732712852875585)
        ·
          refine ⟨91026344346549534639656689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121368459128732712852875585 91026344346549534639656689)
          ·
            refine ⟨68269758259912150979742517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91026344346549534639656689 68269758259912150979742517)
            ·
              refine ⟨6400289836866764154350861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68269758259912150979742517 6400289836866764154350861)
              ·
                refine ⟨2400108688825036557881573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6400289836866764154350861 2400108688825036557881573)
                ·
                  refine ⟨450020379154694354602795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2400108688825036557881573 450020379154694354602795)
                  ·
                    rfl

theorem cell20_985963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_985963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_985963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_985963 prefixEnd_985963 := by exact prefixLift 985963
  have htrace : WordTrace (prefixWord ++ tailWord_985963) baseStart_985963 baseEnd_985963 := by
    simpa [prefixWord, tailWord_985963, baseEnd_985963] using wordTrace_append hprefix tailTrace_985963
  have hstable : (prefixWord ++ tailWord_985963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985963).length < 2 ^ (prefixWord ++ tailWord_985963).sum := by decide
  have hdescent : baseEnd_985963 < baseStart_985963 := by decide
  rcases family_descends (prefixWord ++ tailWord_985963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986039 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_986039 : Nat := 118140960795 + 986039 * 2 ^ 59
def prefixEnd_986039 : Nat := 4983230072969 + 3 ^ 40 * 986039 * 2
def baseEnd_986039 : Nat := 450055067625575868069151

theorem tailTrace_986039 : CollatzResearch.WordTrace tailWord_986039 prefixEnd_986039 450055067625575868069151 := by
  unfold tailWord_986039
  simp only [CollatzResearch.WordTrace]
  refine ⟨35963796874756579899137171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23975864583171053266091447 35963796874756579899137171)
  ·
    refine ⟨53945695312134869848705757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35963796874756579899137171 53945695312134869848705757)
    ·
      refine ⟨20229635742050576193264659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53945695312134869848705757 20229635742050576193264659)
      ·
        refine ⟨30344453613075864289896989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20229635742050576193264659 30344453613075864289896989)
        ·
          refine ⟨11379170104903449108711371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30344453613075864289896989 11379170104903449108711371)
          ·
            refine ⟨17068755157355173663067057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11379170104903449108711371 17068755157355173663067057)
            ·
              refine ⟨12801566368016380247300293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17068755157355173663067057 12801566368016380247300293)
              ·
                refine ⟨2400293694003071296368805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12801566368016380247300293 2400293694003071296368805)
                ·
                  refine ⟨450055067625575868069151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2400293694003071296368805 450055067625575868069151)
                  ·
                    rfl

theorem cell20_986039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_986039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986039 prefixEnd_986039 := by exact prefixLift 986039
  have htrace : WordTrace (prefixWord ++ tailWord_986039) baseStart_986039 baseEnd_986039 := by
    simpa [prefixWord, tailWord_986039, baseEnd_986039] using wordTrace_append hprefix tailTrace_986039
  have hstable : (prefixWord ++ tailWord_986039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986039).length < 2 ^ (prefixWord ++ tailWord_986039).sum := by decide
  have hdescent : baseEnd_986039 < baseStart_986039 := by decide
  rcases family_descends (prefixWord ++ tailWord_986039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986066 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_986066 : Nat := 118140960795 + 986066 * 2 ^ 59
def prefixEnd_986066 : Nat := 4983230072969 + 3 ^ 40 * 986066 * 2
def baseEnd_986066 : Nat := 450067391161283774169041

theorem tailTrace_986066 : CollatzResearch.WordTrace tailWord_986066 prefixEnd_986066 450067391161283774169041 := by
  unfold tailWord_986066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8991195411414690877592513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23976521097105842340246701 8991195411414690877592513)
  ·
    refine ⟨6743396558561018158194385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8991195411414690877592513 6743396558561018158194385)
    ·
      refine ⟨5057547418920763618645789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6743396558561018158194385 5057547418920763618645789)
      ·
        refine ⟨1896580282095286356992171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5057547418920763618645789 1896580282095286356992171)
        ·
          refine ⟨2844870423142929535488257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896580282095286356992171 2844870423142929535488257)
          ·
            refine ⟨2133652817357197151616193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2844870423142929535488257 2133652817357197151616193)
            ·
              refine ⟨1600239613017897863712145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133652817357197151616193 1600239613017897863712145)
              ·
                refine ⟨1200179709763423397784109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600239613017897863712145 1200179709763423397784109)
                ·
                  refine ⟨450067391161283774169041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200179709763423397784109 450067391161283774169041)
                  ·
                    rfl

theorem cell20_986066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_986066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986066 prefixEnd_986066 := by exact prefixLift 986066
  have htrace : WordTrace (prefixWord ++ tailWord_986066) baseStart_986066 baseEnd_986066 := by
    simpa [prefixWord, tailWord_986066, baseEnd_986066] using wordTrace_append hprefix tailTrace_986066
  have hstable : (prefixWord ++ tailWord_986066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986066).length < 2 ^ (prefixWord ++ tailWord_986066).sum := by decide
  have hdescent : baseEnd_986066 < baseStart_986066 := by decide
  rcases family_descends (prefixWord ++ tailWord_986066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986069 : List Nat := [1, 3, 2, 3, 3, 2, 2, 2, 2]
def baseStart_986069 : Nat := 118140960795 + 986069 * 2 ^ 59
def prefixEnd_986069 : Nat := 4983230072969 + 3 ^ 40 * 986069 * 2
def baseEnd_986069 : Nat := 450068760443029097069029

theorem tailTrace_986069 : CollatzResearch.WordTrace tailWord_986069 prefixEnd_986069 450068760443029097069029 := by
  unfold tailWord_986069
  simp only [CollatzResearch.WordTrace]
  refine ⟨35964891064647895022729261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23976594043098596681819507 35964891064647895022729261)
  ·
    refine ⟨13486834149242960633523473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35964891064647895022729261 13486834149242960633523473)
    ·
      refine ⟨10115125611932220475142605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13486834149242960633523473 10115125611932220475142605)
      ·
        refine ⟨3793172104474582678178477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10115125611932220475142605 3793172104474582678178477)
        ·
          refine ⟨1422439539177968504316929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3793172104474582678178477 1422439539177968504316929)
          ·
            refine ⟨1066829654383476378237697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422439539177968504316929 1066829654383476378237697)
            ·
              refine ⟨800122240787607283678273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066829654383476378237697 800122240787607283678273)
              ·
                refine ⟨600091680590705462758705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800122240787607283678273 600091680590705462758705)
                ·
                  refine ⟨450068760443029097069029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600091680590705462758705 450068760443029097069029)
                  ·
                    rfl

theorem cell20_986069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_986069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986069 prefixEnd_986069 := by exact prefixLift 986069
  have htrace : WordTrace (prefixWord ++ tailWord_986069) baseStart_986069 baseEnd_986069 := by
    simpa [prefixWord, tailWord_986069, baseEnd_986069] using wordTrace_append hprefix tailTrace_986069
  have hstable : (prefixWord ++ tailWord_986069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986069).length < 2 ^ (prefixWord ++ tailWord_986069).sum := by decide
  have hdescent : baseEnd_986069 < baseStart_986069 := by decide
  rcases family_descends (prefixWord ++ tailWord_986069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
