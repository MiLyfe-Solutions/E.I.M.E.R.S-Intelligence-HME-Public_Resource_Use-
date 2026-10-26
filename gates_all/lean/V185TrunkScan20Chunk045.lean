import V185TrunkScan20Chunk044

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_273292 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_273292 : Nat := 118140960795 + 273292 * 2 ^ 59
def prefixEnd_273292 : Nat := 4983230072969 + 3 ^ 40 * 273292 * 2
def baseEnd_273292 : Nat := 124737915581022202216141

theorem tailTrace_273292 : CollatzResearch.WordTrace tailWord_273292 prefixEnd_273292 124737915581022202216141 := by
  unfold tailWord_273292
  simp only [CollatzResearch.WordTrace]
  refine ⟨4983889062958616701379065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6645185417278155601838753 4983889062958616701379065)
  ·
    refine ⟨3737916797218962526034299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4983889062958616701379065 3737916797218962526034299)
    ·
      refine ⟨5606875195828443789051449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3737916797218962526034299 5606875195828443789051449)
      ·
        refine ⟨4205156396871332841788587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5606875195828443789051449 4205156396871332841788587)
        ·
          refine ⟨6307734595306999262682881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205156396871332841788587 6307734595306999262682881)
          ·
            refine ⟨4730800946480249447012161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6307734595306999262682881 4730800946480249447012161)
            ·
              refine ⟨3548100709860187085259121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4730800946480249447012161 3548100709860187085259121)
              ·
                refine ⟨2661075532395140313944341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3548100709860187085259121 2661075532395140313944341)
                ·
                  refine ⟨124737915581022202216141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2661075532395140313944341 124737915581022202216141)
                  ·
                    rfl

theorem cell20_273292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_273292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273292 prefixEnd_273292 := by exact prefixLift 273292
  have htrace : WordTrace (prefixWord ++ tailWord_273292) baseStart_273292 baseEnd_273292 := by
    simpa [prefixWord, tailWord_273292, baseEnd_273292] using wordTrace_append hprefix tailTrace_273292
  have hstable : (prefixWord ++ tailWord_273292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273292).length < 2 ^ (prefixWord ++ tailWord_273292).sum := by decide
  have hdescent : baseEnd_273292 < baseStart_273292 := by decide
  rcases family_descends (prefixWord ++ tailWord_273292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273316 : List Nat := [2, 3, 1, 2, 1, 2, 4, 5]
def baseStart_273316 : Nat := 118140960795 + 273316 * 2 ^ 59
def prefixEnd_273316 : Nat := 4983230072969 + 3 ^ 40 * 273316 * 2
def baseEnd_273316 : Nat := 41582956611661595138681

theorem tailTrace_273316 : CollatzResearch.WordTrace tailWord_273316 prefixEnd_273316 41582956611661595138681 := by
  unfold tailWord_273316
  simp only [CollatzResearch.WordTrace]
  refine ⟨4984326738915142750815901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6645768985220190334421201 4984326738915142750815901)
  ·
    refine ⟨1869122527093178531555963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4984326738915142750815901 1869122527093178531555963)
    ·
      refine ⟨2803683790639767797333945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1869122527093178531555963 2803683790639767797333945)
      ·
        refine ⟨2102762842979825848000459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2803683790639767797333945 2102762842979825848000459)
        ·
          refine ⟨3154144264469738772000689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102762842979825848000459 3154144264469738772000689)
          ·
            refine ⟨2365608198352304079000517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3154144264469738772000689 2365608198352304079000517)
            ·
              refine ⟨443551537191057014812597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2365608198352304079000517 443551537191057014812597)
              ·
                refine ⟨41582956611661595138681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 443551537191057014812597 41582956611661595138681)
                ·
                  rfl

theorem cell20_273316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_273316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273316 prefixEnd_273316 := by exact prefixLift 273316
  have htrace : WordTrace (prefixWord ++ tailWord_273316) baseStart_273316 baseEnd_273316 := by
    simpa [prefixWord, tailWord_273316, baseEnd_273316] using wordTrace_append hprefix tailTrace_273316
  have hstable : (prefixWord ++ tailWord_273316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273316).length < 2 ^ (prefixWord ++ tailWord_273316).sum := by decide
  have hdescent : baseEnd_273316 < baseStart_273316 := by decide
  rcases family_descends (prefixWord ++ tailWord_273316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273319 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 3]
def baseStart_273319 : Nat := 118140960795 + 273319 * 2 ^ 59
def prefixEnd_273319 : Nat := 4983230072969 + 3 ^ 40 * 273319 * 2
def baseEnd_273319 : Nat := 124750239116730108316031

theorem tailTrace_273319 : CollatzResearch.WordTrace tailWord_273319 prefixEnd_273319 124750239116730108316031 := by
  unfold tailWord_273319
  simp only [CollatzResearch.WordTrace]
  refine ⟨9968762896819417013991011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6645841931212944675994007 9968762896819417013991011)
  ·
    refine ⟨14953144345229125520986517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9968762896819417013991011 14953144345229125520986517)
    ·
      refine ⟨700928641182615258796243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14953144345229125520986517 700928641182615258796243)
      ·
        refine ⟨1051392961773922888194365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700928641182615258796243 1051392961773922888194365)
        ·
          refine ⟨394272360665221083072887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1051392961773922888194365 394272360665221083072887)
          ·
            refine ⟨591408540997831624609331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394272360665221083072887 591408540997831624609331)
            ·
              refine ⟨887112811496747436913997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591408540997831624609331 887112811496747436913997)
              ·
                refine ⟨332667304311280288842749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 887112811496747436913997 332667304311280288842749)
                ·
                  refine ⟨124750239116730108316031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332667304311280288842749 124750239116730108316031)
                  ·
                    rfl

theorem cell20_273319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 3].length) (baseStart_273319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273319 prefixEnd_273319 := by exact prefixLift 273319
  have htrace : WordTrace (prefixWord ++ tailWord_273319) baseStart_273319 baseEnd_273319 := by
    simpa [prefixWord, tailWord_273319, baseEnd_273319] using wordTrace_append hprefix tailTrace_273319
  have hstable : (prefixWord ++ tailWord_273319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273319).length < 2 ^ (prefixWord ++ tailWord_273319).sum := by decide
  have hdescent : baseEnd_273319 < baseStart_273319 := by decide
  rcases family_descends (prefixWord ++ tailWord_273319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273323 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 3]
def baseStart_273323 : Nat := 118140960795 + 273323 * 2 ^ 59
def prefixEnd_273323 : Nat := 4983230072969 + 3 ^ 40 * 273323 * 2
def baseEnd_273323 : Nat := 124752064825723872182681

theorem tailTrace_273323 : CollatzResearch.WordTrace tailWord_273323 prefixEnd_273323 124752064825723872182681 := by
  unfold tailWord_273323
  simp only [CollatzResearch.WordTrace]
  refine ⟨9968908788804925697136623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6645939192536617131424415 9968908788804925697136623)
  ·
    refine ⟨14953363183207388545704935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9968908788804925697136623 14953363183207388545704935)
    ·
      refine ⟨22430044774811082818557403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14953363183207388545704935 22430044774811082818557403)
      ·
        refine ⟨33645067162216624227836105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22430044774811082818557403 33645067162216624227836105)
        ·
          refine ⟨25233800371662468170877079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33645067162216624227836105 25233800371662468170877079)
          ·
            refine ⟨37850700557493702256315619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25233800371662468170877079 37850700557493702256315619)
            ·
              refine ⟨56776050836240553384473429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37850700557493702256315619 56776050836240553384473429)
              ·
                refine ⟨332672172868596992487149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 56776050836240553384473429 332672172868596992487149)
                ·
                  refine ⟨124752064825723872182681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332672172868596992487149 124752064825723872182681)
                  ·
                    rfl

theorem cell20_273323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 3].length) (baseStart_273323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273323 prefixEnd_273323 := by exact prefixLift 273323
  have htrace : WordTrace (prefixWord ++ tailWord_273323) baseStart_273323 baseEnd_273323 := by
    simpa [prefixWord, tailWord_273323, baseEnd_273323] using wordTrace_append hprefix tailTrace_273323
  have hstable : (prefixWord ++ tailWord_273323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273323).length < 2 ^ (prefixWord ++ tailWord_273323).sum := by decide
  have hdescent : baseEnd_273323 < baseStart_273323 := by decide
  rcases family_descends (prefixWord ++ tailWord_273323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273413 : List Nat := [1, 3, 1, 1, 2, 3, 9]
def baseStart_273413 : Nat := 118140960795 + 273413 * 2 ^ 59
def prefixEnd_273413 : Nat := 4983230072969 + 3 ^ 40 * 273413 * 2
def baseEnd_273413 : Nat := 13865904808675951020257

theorem tailTrace_273413 : CollatzResearch.WordTrace tailWord_273413 prefixEnd_273413 13865904808675951020257 := by
  unfold tailWord_273413
  simp only [CollatzResearch.WordTrace]
  refine ⟨9972191358478871067912893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6648127572319247378608595 9972191358478871067912893)
  ·
    refine ⟨3739571759429576650467335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9972191358478871067912893 3739571759429576650467335)
    ·
      refine ⟨5609357639144364975701003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3739571759429576650467335 5609357639144364975701003)
      ·
        refine ⟨8414036458716547463551505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5609357639144364975701003 8414036458716547463551505)
        ·
          refine ⟨6310527344037410597663629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8414036458716547463551505 6310527344037410597663629)
          ·
            refine ⟨2366447754014028974123861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6310527344037410597663629 2366447754014028974123861)
            ·
              refine ⟨13865904808675951020257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2366447754014028974123861 13865904808675951020257)
              ·
                rfl

theorem cell20_273413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 9].length) (baseStart_273413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273413 prefixEnd_273413 := by exact prefixLift 273413
  have htrace : WordTrace (prefixWord ++ tailWord_273413) baseStart_273413 baseEnd_273413 := by
    simpa [prefixWord, tailWord_273413, baseEnd_273413] using wordTrace_append hprefix tailTrace_273413
  have hstable : (prefixWord ++ tailWord_273413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273413).length < 2 ^ (prefixWord ++ tailWord_273413).sum := by decide
  have hdescent : baseEnd_273413 < baseStart_273413 := by decide
  rcases family_descends (prefixWord ++ tailWord_273413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273416 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 3]
def baseStart_273416 : Nat := 118140960795 + 273416 * 2 ^ 59
def prefixEnd_273416 : Nat := 4983230072969 + 3 ^ 40 * 273416 * 2
def baseEnd_273416 : Nat := 124794512559828882082301

theorem tailTrace_273416 : CollatzResearch.WordTrace tailWord_273416 prefixEnd_273416 124794512559828882082301 := by
  unfold tailWord_273416
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986150388734001290136051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6648200518312001720181401 4986150388734001290136051)
  ·
    refine ⟨7479225583101001935204077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4986150388734001290136051 7479225583101001935204077)
    ·
      refine ⟨2804709593662875725701529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7479225583101001935204077 2804709593662875725701529)
      ·
        refine ⟨2103532195247156794276147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2804709593662875725701529 2103532195247156794276147)
        ·
          refine ⟨3155298292870735191414221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103532195247156794276147 3155298292870735191414221)
          ·
            refine ⟨1183236859826525696780333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3155298292870735191414221 1183236859826525696780333)
            ·
              refine ⟨443713822434947136292625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1183236859826525696780333 443713822434947136292625)
              ·
                refine ⟨332785366826210352219469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443713822434947136292625 332785366826210352219469)
                ·
                  refine ⟨124794512559828882082301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332785366826210352219469 124794512559828882082301)
                  ·
                    rfl

theorem cell20_273416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_273416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273416 prefixEnd_273416 := by exact prefixLift 273416
  have htrace : WordTrace (prefixWord ++ tailWord_273416) baseStart_273416 baseEnd_273416 := by
    simpa [prefixWord, tailWord_273416, baseEnd_273416] using wordTrace_append hprefix tailTrace_273416
  have hstable : (prefixWord ++ tailWord_273416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273416).length < 2 ^ (prefixWord ++ tailWord_273416).sum := by decide
  have hdescent : baseEnd_273416 < baseStart_273416 := by decide
  rcases family_descends (prefixWord ++ tailWord_273416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273447 : List Nat := [1, 1, 7, 1, 1, 2, 1, 6]
def baseStart_273447 : Nat := 118140960795 + 273447 * 2 ^ 59
def prefixEnd_273447 : Nat := 4983230072969 + 3 ^ 40 * 273447 * 2
def baseEnd_273447 : Nat := 41602887268176850682947

theorem tailTrace_273447 : CollatzResearch.WordTrace tailWord_273447 prefixEnd_273447 41602887268176850682947 := by
  unfold tailWord_273447
  simp only [CollatzResearch.WordTrace]
  refine ⟨9973431440355694874650595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6648954293570463249767063 9973431440355694874650595)
  ·
    refine ⟨14960147160533542311975893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9973431440355694874650595 14960147160533542311975893)
    ·
      refine ⟨350628449075004897936935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14960147160533542311975893 350628449075004897936935)
      ·
        refine ⟨525942673612507346905403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350628449075004897936935 525942673612507346905403)
        ·
          refine ⟨788914010418761020358105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525942673612507346905403 788914010418761020358105)
          ·
            refine ⟨591685507814070765268579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788914010418761020358105 591685507814070765268579)
            ·
              refine ⟨887528261721106147902869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591685507814070765268579 887528261721106147902869)
              ·
                refine ⟨41602887268176850682947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 887528261721106147902869 41602887268176850682947)
                ·
                  rfl

theorem cell20_273447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 6].length) (baseStart_273447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273447 prefixEnd_273447 := by exact prefixLift 273447
  have htrace : WordTrace (prefixWord ++ tailWord_273447) baseStart_273447 baseEnd_273447 := by
    simpa [prefixWord, tailWord_273447, baseEnd_273447] using wordTrace_append hprefix tailTrace_273447
  have hstable : (prefixWord ++ tailWord_273447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273447).length < 2 ^ (prefixWord ++ tailWord_273447).sum := by decide
  have hdescent : baseEnd_273447 < baseStart_273447 := by decide
  rcases family_descends (prefixWord ++ tailWord_273447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273451 : List Nat := [1, 1, 1, 1, 2, 1, 7, 6]
def baseStart_273451 : Nat := 118140960795 + 273451 * 2 ^ 59
def prefixEnd_273451 : Nat := 4983230072969 + 3 ^ 40 * 273451 * 2
def baseEnd_273451 : Nat := 41603495837841438638497

theorem tailTrace_273451 : CollatzResearch.WordTrace tailWord_273451 prefixEnd_273451 41603495837841438638497 := by
  unfold tailWord_273451
  simp only [CollatzResearch.WordTrace]
  refine ⟨9973577332341203557796207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6649051554894135705197471 9973577332341203557796207)
  ·
    refine ⟨14960365998511805336694311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9973577332341203557796207 14960365998511805336694311)
    ·
      refine ⟨22440548997767708005041467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14960365998511805336694311 22440548997767708005041467)
      ·
        refine ⟨33660823496651562007562201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22440548997767708005041467 33660823496651562007562201)
        ·
          refine ⟨25245617622488671505671651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33660823496651562007562201 25245617622488671505671651)
          ·
            refine ⟨37868426433733007258507477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25245617622488671505671651 37868426433733007258507477)
            ·
              refine ⟨887541244540617357621269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37868426433733007258507477 887541244540617357621269)
              ·
                refine ⟨41603495837841438638497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 887541244540617357621269 41603495837841438638497)
                ·
                  rfl

theorem cell20_273451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_273451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273451 prefixEnd_273451 := by exact prefixLift 273451
  have htrace : WordTrace (prefixWord ++ tailWord_273451) baseStart_273451 baseEnd_273451 := by
    simpa [prefixWord, tailWord_273451, baseEnd_273451] using wordTrace_append hprefix tailTrace_273451
  have hstable : (prefixWord ++ tailWord_273451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273451).length < 2 ^ (prefixWord ++ tailWord_273451).sum := by decide
  have hdescent : baseEnd_273451 < baseStart_273451 := by decide
  rcases family_descends (prefixWord ++ tailWord_273451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273468 : List Nat := [2, 2, 2, 2, 2, 4, 6]
def baseStart_273468 : Nat := 118140960795 + 273468 * 2 ^ 59
def prefixEnd_273468 : Nat := 4983230072969 + 3 ^ 40 * 273468 * 2
def baseEnd_273468 : Nat := 13868694086305312483195

theorem tailTrace_273468 : CollatzResearch.WordTrace tailWord_273468 prefixEnd_273468 13868694086305312483195 := by
  unfold tailWord_273468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4987098686639807730582529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6649464915519743640776705 4987098686639807730582529)
  ·
    refine ⟨3740324014979855797936897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4987098686639807730582529 3740324014979855797936897)
    ·
      refine ⟨2805243011234891848452673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3740324014979855797936897 2805243011234891848452673)
      ·
        refine ⟨2103932258426168886339505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2805243011234891848452673 2103932258426168886339505)
        ·
          refine ⟨1577949193819626664754629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2103932258426168886339505 1577949193819626664754629)
          ·
            refine ⟨295865473841179999641493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1577949193819626664754629 295865473841179999641493)
            ·
              refine ⟨13868694086305312483195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 295865473841179999641493 13868694086305312483195)
              ·
                rfl

theorem cell20_273468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 6].length) (baseStart_273468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273468 prefixEnd_273468 := by exact prefixLift 273468
  have htrace : WordTrace (prefixWord ++ tailWord_273468) baseStart_273468 baseEnd_273468 := by
    simpa [prefixWord, tailWord_273468, baseEnd_273468] using wordTrace_append hprefix tailTrace_273468
  have hstable : (prefixWord ++ tailWord_273468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273468).length < 2 ^ (prefixWord ++ tailWord_273468).sum := by decide
  have hdescent : baseEnd_273468 < baseStart_273468 := by decide
  rcases family_descends (prefixWord ++ tailWord_273468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273475 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 3]
def baseStart_273475 : Nat := 118140960795 + 273475 * 2 ^ 59
def prefixEnd_273475 : Nat := 4983230072969 + 3 ^ 40 * 273475 * 2
def baseEnd_273475 : Nat := 124821441767486899115393

theorem tailTrace_273475 : CollatzResearch.WordTrace tailWord_273475 prefixEnd_273475 124821441767486899115393 := by
  unfold tailWord_273475
  simp only [CollatzResearch.WordTrace]
  refine ⟨9974452684254255656669879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6649635122836170437779919 9974452684254255656669879)
  ·
    refine ⟨14961679026381383485004819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9974452684254255656669879 14961679026381383485004819)
    ·
      refine ⟨22442518539572075227507229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14961679026381383485004819 22442518539572075227507229)
      ·
        refine ⟨8415944452339528210315211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22442518539572075227507229 8415944452339528210315211)
        ·
          refine ⟨12623916678509292315472817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8415944452339528210315211 12623916678509292315472817)
          ·
            refine ⟨9467937508881969236604613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12623916678509292315472817 9467937508881969236604613)
            ·
              refine ⟨1775238282915369231863365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9467937508881969236604613 1775238282915369231863365)
              ·
                refine ⟨332857178046631730974381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1775238282915369231863365 332857178046631730974381)
                ·
                  refine ⟨124821441767486899115393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332857178046631730974381 124821441767486899115393)
                  ·
                    rfl

theorem cell20_273475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 3].length) (baseStart_273475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273475 prefixEnd_273475 := by exact prefixLift 273475
  have htrace : WordTrace (prefixWord ++ tailWord_273475) baseStart_273475 baseEnd_273475 := by
    simpa [prefixWord, tailWord_273475, baseEnd_273475] using wordTrace_append hprefix tailTrace_273475
  have hstable : (prefixWord ++ tailWord_273475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273475).length < 2 ^ (prefixWord ++ tailWord_273475).sum := by decide
  have hdescent : baseEnd_273475 < baseStart_273475 := by decide
  rcases family_descends (prefixWord ++ tailWord_273475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273485 : List Nat := [1, 6, 1, 1, 1, 3, 2, 5]
def baseStart_273485 : Nat := 118140960795 + 273485 * 2 ^ 59
def prefixEnd_273485 : Nat := 4983230072969 + 3 ^ 40 * 273485 * 2
def baseEnd_273485 : Nat := 41608668679990436260673

theorem tailTrace_273485 : CollatzResearch.WordTrace tailWord_273485 prefixEnd_273485 41608668679990436260673 := by
  unfold tailWord_273485
  simp only [CollatzResearch.WordTrace]
  refine ⟨9974817414218027364533909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6649878276145351576355939 9974817414218027364533909)
  ·
    refine ⟨467569566291470032712527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9974817414218027364533909 467569566291470032712527)
    ·
      refine ⟨701354349437205049068791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467569566291470032712527 701354349437205049068791)
      ·
        refine ⟨1052031524155807573603187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701354349437205049068791 1052031524155807573603187)
        ·
          refine ⟨1578047286233711360404781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052031524155807573603187 1578047286233711360404781)
          ·
            refine ⟨591767732337641760151793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1578047286233711360404781 591767732337641760151793)
            ·
              refine ⟨443825799253231320113845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591767732337641760151793 443825799253231320113845)
              ·
                refine ⟨41608668679990436260673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 443825799253231320113845 41608668679990436260673)
                ·
                  rfl

theorem cell20_273485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_273485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273485 prefixEnd_273485 := by exact prefixLift 273485
  have htrace : WordTrace (prefixWord ++ tailWord_273485) baseStart_273485 baseEnd_273485 := by
    simpa [prefixWord, tailWord_273485, baseEnd_273485] using wordTrace_append hprefix tailTrace_273485
  have hstable : (prefixWord ++ tailWord_273485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273485).length < 2 ^ (prefixWord ++ tailWord_273485).sum := by decide
  have hdescent : baseEnd_273485 < baseStart_273485 := by decide
  rcases family_descends (prefixWord ++ tailWord_273485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273489 : List Nat := [1, 2, 2, 1, 3, 1, 3, 7]
def baseStart_273489 : Nat := 118140960795 + 273489 * 2 ^ 59
def prefixEnd_273489 : Nat := 4983230072969 + 3 ^ 40 * 273489 * 2
def baseEnd_273489 : Nat := 41609277249655024216223

theorem tailTrace_273489 : CollatzResearch.WordTrace tailWord_273489 prefixEnd_273489 41609277249655024216223 := by
  unfold tailWord_273489
  simp only [CollatzResearch.WordTrace]
  refine ⟨9974963306203536047679521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6649975537469024031786347 9974963306203536047679521)
  ·
    refine ⟨7481222479652652035759641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9974963306203536047679521 7481222479652652035759641)
    ·
      refine ⟨5610916859739489026819731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7481222479652652035759641 5610916859739489026819731)
      ·
        refine ⟨8416375289609233540229597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5610916859739489026819731 8416375289609233540229597)
        ·
          refine ⟨3156140733603462577586099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8416375289609233540229597 3156140733603462577586099)
          ·
            refine ⟨4734211100405193866379149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156140733603462577586099 4734211100405193866379149)
            ·
              refine ⟨1775329162651947699892181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4734211100405193866379149 1775329162651947699892181)
              ·
                refine ⟨41609277249655024216223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1775329162651947699892181 41609277249655024216223)
                ·
                  rfl

theorem cell20_273489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_273489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273489 prefixEnd_273489 := by exact prefixLift 273489
  have htrace : WordTrace (prefixWord ++ tailWord_273489) baseStart_273489 baseEnd_273489 := by
    simpa [prefixWord, tailWord_273489, baseEnd_273489] using wordTrace_append hprefix tailTrace_273489
  have hstable : (prefixWord ++ tailWord_273489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273489).length < 2 ^ (prefixWord ++ tailWord_273489).sum := by decide
  have hdescent : baseEnd_273489 < baseStart_273489 := by decide
  rcases family_descends (prefixWord ++ tailWord_273489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273502 : List Nat := [4, 4, 1, 1, 1, 1, 2, 6]
def baseStart_273502 : Nat := 118140960795 + 273502 * 2 ^ 59
def prefixEnd_273502 : Nat := 4983230072969 + 3 ^ 40 * 273502 * 2
def baseEnd_273502 : Nat := 41611255101064935071761

theorem tailTrace_273502 : CollatzResearch.WordTrace tailWord_273502 prefixEnd_273502 41611255101064935071761 := by
  unfold tailWord_273502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246929681894554908487845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6650291636770959511935173 1246929681894554908487845)
  ·
    refine ⟨233799315355229045341471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1246929681894554908487845 233799315355229045341471)
    ·
      refine ⟨350698973032843568012207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233799315355229045341471 350698973032843568012207)
      ·
        refine ⟨526048459549265352018311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350698973032843568012207 526048459549265352018311)
        ·
          refine ⟨789072689323898028027467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526048459549265352018311 789072689323898028027467)
          ·
            refine ⟨1183609033985847042041201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789072689323898028027467 1183609033985847042041201)
            ·
              refine ⟨887706775489385281530901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183609033985847042041201 887706775489385281530901)
              ·
                refine ⟨41611255101064935071761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 887706775489385281530901 41611255101064935071761)
                ·
                  rfl

theorem cell20_273502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_273502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273502 prefixEnd_273502 := by exact prefixLift 273502
  have htrace : WordTrace (prefixWord ++ tailWord_273502) baseStart_273502 baseEnd_273502 := by
    simpa [prefixWord, tailWord_273502, baseEnd_273502] using wordTrace_append hprefix tailTrace_273502
  have hstable : (prefixWord ++ tailWord_273502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273502).length < 2 ^ (prefixWord ++ tailWord_273502).sum := by decide
  have hdescent : baseEnd_273502 < baseStart_273502 := by decide
  rcases family_descends (prefixWord ++ tailWord_273502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273585 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 3]
def baseStart_273585 : Nat := 118140960795 + 273585 * 2 ^ 59
def prefixEnd_273585 : Nat := 4983230072969 + 3 ^ 40 * 273585 * 2
def baseEnd_273585 : Nat := 124871648764815405448277

theorem tailTrace_273585 : CollatzResearch.WordTrace tailWord_273585 prefixEnd_273585 124871648764815405448277 := by
  unfold tailWord_273585
  simp only [CollatzResearch.WordTrace]
  refine ⟨9978464713855744443174209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6652309809237162962116139 9978464713855744443174209)
  ·
    refine ⟨7483848535391808332380657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9978464713855744443174209 7483848535391808332380657)
    ·
      refine ⟨5612886401543856249285493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7483848535391808332380657 5612886401543856249285493)
      ·
        refine ⟨526208100144736523370515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5612886401543856249285493 526208100144736523370515)
        ·
          refine ⟨789312150217104785055773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526208100144736523370515 789312150217104785055773)
          ·
            refine ⟨295992056331414294395915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 789312150217104785055773 295992056331414294395915)
            ·
              refine ⟨443988084497121441593873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295992056331414294395915 443988084497121441593873)
              ·
                refine ⟨332991063372841081195405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443988084497121441593873 332991063372841081195405)
                ·
                  refine ⟨124871648764815405448277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332991063372841081195405 124871648764815405448277)
                  ·
                    rfl

theorem cell20_273585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_273585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273585 prefixEnd_273585 := by exact prefixLift 273585
  have htrace : WordTrace (prefixWord ++ tailWord_273585) baseStart_273585 baseEnd_273585 := by
    simpa [prefixWord, tailWord_273585, baseEnd_273585] using wordTrace_append hprefix tailTrace_273585
  have hstable : (prefixWord ++ tailWord_273585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273585).length < 2 ^ (prefixWord ++ tailWord_273585).sum := by decide
  have hdescent : baseEnd_273585 < baseStart_273585 := by decide
  rcases family_descends (prefixWord ++ tailWord_273585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273637 : List Nat := [1, 3, 1, 4, 4, 1, 6]
def baseStart_273637 : Nat := 118140960795 + 273637 * 2 ^ 59
def prefixEnd_273637 : Nat := 4983230072969 + 3 ^ 40 * 273637 * 2
def baseEnd_273637 : Nat := 13877264775748259523859

theorem tailTrace_273637 : CollatzResearch.WordTrace tailWord_273637 prefixEnd_273637 13877264775748259523859 := by
  unfold tailWord_273637
  simp only [CollatzResearch.WordTrace]
  refine ⟨9980361309667357324067165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6653574206444904882711443 9980361309667357324067165)
  ·
    refine ⟨3742635491125258996525187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9980361309667357324067165 3742635491125258996525187)
    ·
      refine ⟨5613953236687888494787781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3742635491125258996525187 5613953236687888494787781)
      ·
        refine ⟨1052616231878979092772709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5613953236687888494787781 1052616231878979092772709)
        ·
          refine ⟨197365543477308579894883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1052616231878979092772709 197365543477308579894883)
          ·
            refine ⟨296048315215962869842325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197365543477308579894883 296048315215962869842325)
            ·
              refine ⟨13877264775748259523859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 296048315215962869842325 13877264775748259523859)
              ·
                rfl

theorem cell20_273637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 6].length) (baseStart_273637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273637 prefixEnd_273637 := by exact prefixLift 273637
  have htrace : WordTrace (prefixWord ++ tailWord_273637) baseStart_273637 baseEnd_273637 := by
    simpa [prefixWord, tailWord_273637, baseEnd_273637] using wordTrace_append hprefix tailTrace_273637
  have hstable : (prefixWord ++ tailWord_273637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273637).length < 2 ^ (prefixWord ++ tailWord_273637).sum := by decide
  have hdescent : baseEnd_273637 < baseStart_273637 := by decide
  rcases family_descends (prefixWord ++ tailWord_273637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273647 : List Nat := [1, 1, 2, 1, 7, 1, 3, 2, 2]
def baseStart_273647 : Nat := 118140960795 + 273647 * 2 ^ 59
def prefixEnd_273647 : Nat := 4983230072969 + 3 ^ 40 * 273647 * 2
def baseEnd_273647 : Nat := 124899947254218745381357

theorem tailTrace_273647 : CollatzResearch.WordTrace tailWord_273647 prefixEnd_273647 124899947254218745381357 := by
  unfold tailWord_273647
  simp only [CollatzResearch.WordTrace]
  refine ⟨9980726039631129031931195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6653817359754086021287463 9980726039631129031931195)
  ·
    refine ⟨14971089059446693547896793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9980726039631129031931195 14971089059446693547896793)
    ·
      refine ⟨11228316794585020160922595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14971089059446693547896793 11228316794585020160922595)
      ·
        refine ⟨16842475191877530241383893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11228316794585020160922595 16842475191877530241383893)
        ·
          refine ⟨394745512309629615032435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16842475191877530241383893 394745512309629615032435)
          ·
            refine ⟨592118268464444422548653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394745512309629615032435 592118268464444422548653)
            ·
              refine ⟨222044350674166658455745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 592118268464444422548653 222044350674166658455745)
              ·
                refine ⟨166533263005624993841809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222044350674166658455745 166533263005624993841809)
                ·
                  refine ⟨124899947254218745381357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166533263005624993841809 124899947254218745381357)
                  ·
                    rfl

theorem cell20_273647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 2].length) (baseStart_273647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273647 prefixEnd_273647 := by exact prefixLift 273647
  have htrace : WordTrace (prefixWord ++ tailWord_273647) baseStart_273647 baseEnd_273647 := by
    simpa [prefixWord, tailWord_273647, baseEnd_273647] using wordTrace_append hprefix tailTrace_273647
  have hstable : (prefixWord ++ tailWord_273647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273647).length < 2 ^ (prefixWord ++ tailWord_273647).sum := by decide
  have hdescent : baseEnd_273647 < baseStart_273647 := by decide
  rcases family_descends (prefixWord ++ tailWord_273647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273651 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 4]
def baseStart_273651 : Nat := 118140960795 + 273651 * 2 ^ 59
def prefixEnd_273651 : Nat := 4983230072969 + 3 ^ 40 * 273651 * 2
def baseEnd_273651 : Nat := 124901772963212509248007

theorem tailTrace_273651 : CollatzResearch.WordTrace tailWord_273651 prefixEnd_273651 124901772963212509248007 := by
  unfold tailWord_273651
  simp only [CollatzResearch.WordTrace]
  refine ⟨9980871931616637715076807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6653914621077758476717871 9980871931616637715076807)
  ·
    refine ⟨14971307897424956572615211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9980871931616637715076807 14971307897424956572615211)
    ·
      refine ⟨22456961846137434858922817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14971307897424956572615211 22456961846137434858922817)
      ·
        refine ⟨16842721384603076144192113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22456961846137434858922817 16842721384603076144192113)
        ·
          refine ⟨12632041038452307108144085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16842721384603076144192113 12632041038452307108144085)
          ·
            refine ⟨296063461838725947847127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 12632041038452307108144085 296063461838725947847127)
            ·
              refine ⟨444095192758088921770691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296063461838725947847127 444095192758088921770691)
              ·
                refine ⟨666142789137133382656037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444095192758088921770691 666142789137133382656037)
                ·
                  refine ⟨124901772963212509248007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 666142789137133382656037 124901772963212509248007)
                  ·
                    rfl

theorem cell20_273651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 4].length) (baseStart_273651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273651 prefixEnd_273651 := by exact prefixLift 273651
  have htrace : WordTrace (prefixWord ++ tailWord_273651) baseStart_273651 baseEnd_273651 := by
    simpa [prefixWord, tailWord_273651, baseEnd_273651] using wordTrace_append hprefix tailTrace_273651
  have hstable : (prefixWord ++ tailWord_273651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273651).length < 2 ^ (prefixWord ++ tailWord_273651).sum := by decide
  have hdescent : baseEnd_273651 < baseStart_273651 := by decide
  rcases family_descends (prefixWord ++ tailWord_273651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273696 : List Nat := [2, 1, 1, 5, 4, 7]
def baseStart_273696 : Nat := 118140960795 + 273696 * 2 ^ 59
def prefixEnd_273696 : Nat := 4983230072969 + 3 ^ 40 * 273696 * 2
def baseEnd_273696 : Nat := 4626752303310827879549

theorem tailTrace_273696 : CollatzResearch.WordTrace tailWord_273696 prefixEnd_273696 4626752303310827879549 := by
  unfold tailWord_273696
  simp only [CollatzResearch.WordTrace]
  refine ⟨4991256608226805200232471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6655008810969073600309961 4991256608226805200232471)
  ·
    refine ⟨7486884912340207800348707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4991256608226805200232471 7486884912340207800348707)
    ·
      refine ⟨11230327368510311700523061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7486884912340207800348707 11230327368510311700523061)
      ·
        refine ⟨1052843190797841721924037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11230327368510311700523061 1052843190797841721924037)
        ·
          refine ⟨197408098274595322860757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1052843190797841721924037 197408098274595322860757)
          ·
            refine ⟨4626752303310827879549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 197408098274595322860757 4626752303310827879549)
            ·
              rfl

theorem cell20_273696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 7].length) (baseStart_273696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273696 prefixEnd_273696 := by exact prefixLift 273696
  have htrace : WordTrace (prefixWord ++ tailWord_273696) baseStart_273696 baseEnd_273696 := by
    simpa [prefixWord, tailWord_273696, baseEnd_273696] using wordTrace_append hprefix tailTrace_273696
  have hstable : (prefixWord ++ tailWord_273696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273696).length < 2 ^ (prefixWord ++ tailWord_273696).sum := by decide
  have hdescent : baseEnd_273696 < baseStart_273696 := by decide
  rcases family_descends (prefixWord ++ tailWord_273696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273748 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_273748 : Nat := 118140960795 + 273748 * 2 ^ 59
def prefixEnd_273748 : Nat := 4983230072969 + 3 ^ 40 * 273748 * 2
def baseEnd_273748 : Nat := 124946046406311283014277

theorem tailTrace_273748 : CollatzResearch.WordTrace tailWord_273748 prefixEnd_273748 124946046406311283014277 := by
  unfold tailWord_273748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4992204906132611640678949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6656273208176815520905265 4992204906132611640678949)
  ·
    refine ⟨936038419899864682627303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4992204906132611640678949 936038419899864682627303)
    ·
      refine ⟨1404057629849797023940955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 936038419899864682627303 1404057629849797023940955)
      ·
        refine ⟨2106086444774695535911433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404057629849797023940955 2106086444774695535911433)
        ·
          refine ⟨1579564833581021651933575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2106086444774695535911433 1579564833581021651933575)
          ·
            refine ⟨2369347250371532477900363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579564833581021651933575 2369347250371532477900363)
            ·
              refine ⟨3554020875557298716850545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369347250371532477900363 3554020875557298716850545)
              ·
                refine ⟨2665515656667974037637909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3554020875557298716850545 2665515656667974037637909)
                ·
                  refine ⟨124946046406311283014277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2665515656667974037637909 124946046406311283014277)
                  ·
                    rfl

theorem cell20_273748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_273748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273748 prefixEnd_273748 := by exact prefixLift 273748
  have htrace : WordTrace (prefixWord ++ tailWord_273748) baseStart_273748 baseEnd_273748 := by
    simpa [prefixWord, tailWord_273748, baseEnd_273748] using wordTrace_append hprefix tailTrace_273748
  have hstable : (prefixWord ++ tailWord_273748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273748).length < 2 ^ (prefixWord ++ tailWord_273748).sum := by decide
  have hdescent : baseEnd_273748 < baseStart_273748 := by decide
  rcases family_descends (prefixWord ++ tailWord_273748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273750 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_273750 : Nat := 118140960795 + 273750 * 2 ^ 59
def prefixEnd_273750 : Nat := 4983230072969 + 3 ^ 40 * 273750 * 2
def baseEnd_273750 : Nat := 124946959260808164947603

theorem tailTrace_273750 : CollatzResearch.WordTrace tailWord_273750 prefixEnd_273750 124946959260808164947603 := by
  unfold tailWord_273750
  simp only [CollatzResearch.WordTrace]
  refine ⟨624030172391123601433169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6656321838838651748620469 624030172391123601433169)
  ·
    refine ⟨468022629293342701074877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 624030172391123601433169 468022629293342701074877)
    ·
      refine ⟨175508485985003512903079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 468022629293342701074877 175508485985003512903079)
      ·
        refine ⟨263262728977505269354619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175508485985003512903079 263262728977505269354619)
        ·
          refine ⟨394894093466257904031929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263262728977505269354619 394894093466257904031929)
          ·
            refine ⟨296170570099693428023947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394894093466257904031929 296170570099693428023947)
            ·
              refine ⟨444255855149540142035921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296170570099693428023947 444255855149540142035921)
              ·
                refine ⟨333191891362155106526941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444255855149540142035921 333191891362155106526941)
                ·
                  refine ⟨124946959260808164947603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333191891362155106526941 124946959260808164947603)
                  ·
                    rfl

theorem cell20_273750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_273750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273750 prefixEnd_273750 := by exact prefixLift 273750
  have htrace : WordTrace (prefixWord ++ tailWord_273750) baseStart_273750 baseEnd_273750 := by
    simpa [prefixWord, tailWord_273750, baseEnd_273750] using wordTrace_append hprefix tailTrace_273750
  have hstable : (prefixWord ++ tailWord_273750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273750).length < 2 ^ (prefixWord ++ tailWord_273750).sum := by decide
  have hdescent : baseEnd_273750 < baseStart_273750 := by decide
  rcases family_descends (prefixWord ++ tailWord_273750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273765 : List Nat := [1, 3, 1, 3, 1, 2, 1, 6, 2]
def baseStart_273765 : Nat := 118140960795 + 273765 * 2 ^ 59
def prefixEnd_273765 : Nat := 4983230072969 + 3 ^ 40 * 273765 * 2
def baseEnd_273765 : Nat := 124953805669534779447541

theorem tailTrace_273765 : CollatzResearch.WordTrace tailWord_273765 prefixEnd_273765 124953805669534779447541 := by
  unfold tailWord_273765
  simp only [CollatzResearch.WordTrace]
  refine ⟨9985029853203635184726749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6656686568802423456484499 9985029853203635184726749)
  ·
    refine ⟨3744386194951363194272531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9985029853203635184726749 3744386194951363194272531)
    ·
      refine ⟨5616579292427044791408797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3744386194951363194272531 5616579292427044791408797)
      ·
        refine ⟨2106217234660141796778299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5616579292427044791408797 2106217234660141796778299)
        ·
          refine ⟨3159325851990212695167449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106217234660141796778299 3159325851990212695167449)
          ·
            refine ⟨2369494388992659521375587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3159325851990212695167449 2369494388992659521375587)
            ·
              refine ⟨3554241583488989282063381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369494388992659521375587 3554241583488989282063381)
              ·
                refine ⟨166605074226046372596721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3554241583488989282063381 166605074226046372596721)
                ·
                  refine ⟨124953805669534779447541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166605074226046372596721 124953805669534779447541)
                  ·
                    rfl

theorem cell20_273765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_273765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273765 prefixEnd_273765 := by exact prefixLift 273765
  have htrace : WordTrace (prefixWord ++ tailWord_273765) baseStart_273765 baseEnd_273765 := by
    simpa [prefixWord, tailWord_273765, baseEnd_273765] using wordTrace_append hprefix tailTrace_273765
  have hstable : (prefixWord ++ tailWord_273765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273765).length < 2 ^ (prefixWord ++ tailWord_273765).sum := by decide
  have hdescent : baseEnd_273765 < baseStart_273765 := by decide
  rcases family_descends (prefixWord ++ tailWord_273765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273914 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_273914 : Nat := 118140960795 + 273914 * 2 ^ 59
def prefixEnd_273914 : Nat := 4983230072969 + 3 ^ 40 * 273914 * 2
def baseEnd_273914 : Nat := 125021813329552483480265

theorem tailTrace_273914 : CollatzResearch.WordTrace tailWord_273914 prefixEnd_273914 125021813329552483480265 := by
  unfold tailWord_273914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2497616082415958407975199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6660309553109222421267197 2497616082415958407975199)
  ·
    refine ⟨3746424123623937611962799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2497616082415958407975199 3746424123623937611962799)
    ·
      refine ⟨5619636185435906417944199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3746424123623937611962799 5619636185435906417944199)
      ·
        refine ⟨8429454278153859626916299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5619636185435906417944199 8429454278153859626916299)
        ·
          refine ⟨12644181417230789440374449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8429454278153859626916299 12644181417230789440374449)
          ·
            refine ⟨9483136062923092080280837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12644181417230789440374449 9483136062923092080280837)
            ·
              refine ⟨1778088011798079765052657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9483136062923092080280837 1778088011798079765052657)
              ·
                refine ⟨1333566008848559823789493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778088011798079765052657 1333566008848559823789493)
                ·
                  refine ⟨125021813329552483480265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1333566008848559823789493 125021813329552483480265)
                  ·
                    rfl

theorem cell20_273914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_273914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273914 prefixEnd_273914 := by exact prefixLift 273914
  have htrace : WordTrace (prefixWord ++ tailWord_273914) baseStart_273914 baseEnd_273914 := by
    simpa [prefixWord, tailWord_273914, baseEnd_273914] using wordTrace_append hprefix tailTrace_273914
  have hstable : (prefixWord ++ tailWord_273914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273914).length < 2 ^ (prefixWord ++ tailWord_273914).sum := by decide
  have hdescent : baseEnd_273914 < baseStart_273914 := by decide
  rcases family_descends (prefixWord ++ tailWord_273914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273917 : List Nat := [1, 4, 1, 1, 1, 4, 1, 5, 2]
def baseStart_273917 : Nat := 118140960795 + 273917 * 2 ^ 59
def prefixEnd_273917 : Nat := 4983230072969 + 3 ^ 40 * 273917 * 2
def baseEnd_273917 : Nat := 125023182611297806380253

theorem tailTrace_273917 : CollatzResearch.WordTrace tailWord_273917 prefixEnd_273917 125023182611297806380253 := by
  unfold tailWord_273917
  simp only [CollatzResearch.WordTrace]
  refine ⟨9990573748652965144260005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6660382499101976762840003 9990573748652965144260005)
  ·
    refine ⟨1873232577872430964548751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9990573748652965144260005 1873232577872430964548751)
    ·
      refine ⟨2809848866808646446823127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873232577872430964548751 2809848866808646446823127)
      ·
        refine ⟨4214773300212969670234691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2809848866808646446823127 4214773300212969670234691)
        ·
          refine ⟨6322159950319454505352037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4214773300212969670234691 6322159950319454505352037)
          ·
            refine ⟨1185404990684897719753507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6322159950319454505352037 1185404990684897719753507)
            ·
              refine ⟨1778107486027346579630261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185404990684897719753507 1778107486027346579630261)
              ·
                refine ⟨166697576815063741840337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1778107486027346579630261 166697576815063741840337)
                ·
                  refine ⟨125023182611297806380253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166697576815063741840337 125023182611297806380253)
                  ·
                    rfl

theorem cell20_273917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_273917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273917 prefixEnd_273917 := by exact prefixLift 273917
  have htrace : WordTrace (prefixWord ++ tailWord_273917) baseStart_273917 baseEnd_273917 := by
    simpa [prefixWord, tailWord_273917, baseEnd_273917] using wordTrace_append hprefix tailTrace_273917
  have hstable : (prefixWord ++ tailWord_273917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273917).length < 2 ^ (prefixWord ++ tailWord_273917).sum := by decide
  have hdescent : baseEnd_273917 < baseStart_273917 := by decide
  rcases family_descends (prefixWord ++ tailWord_273917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273924 : List Nat := [2, 3, 2, 3, 2, 1, 7]
def baseStart_273924 : Nat := 118140960795 + 273924 * 2 ^ 59
def prefixEnd_273924 : Nat := 4983230072969 + 3 ^ 40 * 273924 * 2
def baseEnd_273924 : Nat := 13891819733559654794099

theorem tailTrace_273924 : CollatzResearch.WordTrace tailWord_273924 prefixEnd_273924 13891819733559654794099 := by
  unfold tailWord_273924
  simp only [CollatzResearch.WordTrace]
  refine ⟨4995414529813802669882413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6660552706418403559843217 4995414529813802669882413)
  ·
    refine ⟨1873280448680176001205905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4995414529813802669882413 1873280448680176001205905)
    ·
      refine ⟨1404960336510132000904429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1873280448680176001205905 1404960336510132000904429)
      ·
        refine ⟨526860126191299500339161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1404960336510132000904429 526860126191299500339161)
        ·
          refine ⟨395145094643474625254371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526860126191299500339161 395145094643474625254371)
          ·
            refine ⟨592717641965211937881557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395145094643474625254371 592717641965211937881557)
            ·
              refine ⟨13891819733559654794099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 592717641965211937881557 13891819733559654794099)
              ·
                rfl

theorem cell20_273924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 7].length) (baseStart_273924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273924 prefixEnd_273924 := by exact prefixLift 273924
  have htrace : WordTrace (prefixWord ++ tailWord_273924) baseStart_273924 baseEnd_273924 := by
    simpa [prefixWord, tailWord_273924, baseEnd_273924] using wordTrace_append hprefix tailTrace_273924
  have hstable : (prefixWord ++ tailWord_273924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273924).length < 2 ^ (prefixWord ++ tailWord_273924).sum := by decide
  have hdescent : baseEnd_273924 < baseStart_273924 := by decide
  rcases family_descends (prefixWord ++ tailWord_273924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273931 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 5]
def baseStart_273931 : Nat := 118140960795 + 273931 * 2 ^ 59
def prefixEnd_273931 : Nat := 4983230072969 + 3 ^ 40 * 273931 * 2
def baseEnd_273931 : Nat := 125029572592775979913529

theorem tailTrace_273931 : CollatzResearch.WordTrace tailWord_273931 prefixEnd_273931 125029572592775979913529 := by
  unfold tailWord_273931
  simp only [CollatzResearch.WordTrace]
  refine ⟨9991084370602245535269647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6660722913734830356846431 9991084370602245535269647)
  ·
    refine ⟨14986626555903368302904471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9991084370602245535269647 14986626555903368302904471)
    ·
      refine ⟨22479939833855052454356707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14986626555903368302904471 22479939833855052454356707)
      ·
        refine ⟨33719909750782578681535061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22479939833855052454356707 33719909750782578681535061)
        ·
          refine ⟨395155192391983343924239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 33719909750782578681535061 395155192391983343924239)
          ·
            refine ⟨592732788587975015886359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395155192391983343924239 592732788587975015886359)
            ·
              refine ⟨889099182881962523829539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592732788587975015886359 889099182881962523829539)
              ·
                refine ⟨1333648774322943785744309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889099182881962523829539 1333648774322943785744309)
                ·
                  refine ⟨125029572592775979913529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1333648774322943785744309 125029572592775979913529)
                  ·
                    rfl

theorem cell20_273931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 5].length) (baseStart_273931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273931 prefixEnd_273931 := by exact prefixLift 273931
  have htrace : WordTrace (prefixWord ++ tailWord_273931) baseStart_273931 baseEnd_273931 := by
    simpa [prefixWord, tailWord_273931, baseEnd_273931] using wordTrace_append hprefix tailTrace_273931
  have hstable : (prefixWord ++ tailWord_273931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273931).length < 2 ^ (prefixWord ++ tailWord_273931).sum := by decide
  have hdescent : baseEnd_273931 < baseStart_273931 := by decide
  rcases family_descends (prefixWord ++ tailWord_273931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273948 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 3]
def baseStart_273948 : Nat := 118140960795 + 273948 * 2 ^ 59
def prefixEnd_273948 : Nat := 4983230072969 + 3 ^ 40 * 273948 * 2
def baseEnd_273948 : Nat := 125037331855999476346793

theorem tailTrace_273948 : CollatzResearch.WordTrace tailWord_273948 prefixEnd_273948 125037331855999476346793 := by
  unfold tailWord_273948
  simp only [CollatzResearch.WordTrace]
  refine ⟨4995852205770328719319249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6661136274360438292425665 4995852205770328719319249)
  ·
    refine ⟨3746889154327746539489437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4995852205770328719319249 3746889154327746539489437)
    ·
      refine ⟨1405083432872904952308539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3746889154327746539489437 1405083432872904952308539)
      ·
        refine ⟨2107625149309357428462809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1405083432872904952308539 2107625149309357428462809)
        ·
          refine ⟨1580718861982018071347107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2107625149309357428462809 1580718861982018071347107)
          ·
            refine ⟨2371078292973027107020661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580718861982018071347107 2371078292973027107020661)
            ·
              refine ⟨222288589966221291283187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2371078292973027107020661 222288589966221291283187)
              ·
                refine ⟨333432884949331936924781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222288589966221291283187 333432884949331936924781)
                ·
                  refine ⟨125037331855999476346793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333432884949331936924781 125037331855999476346793)
                  ·
                    rfl

theorem cell20_273948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_273948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273948 prefixEnd_273948 := by exact prefixLift 273948
  have htrace : WordTrace (prefixWord ++ tailWord_273948) baseStart_273948 baseEnd_273948 := by
    simpa [prefixWord, tailWord_273948, baseEnd_273948] using wordTrace_append hprefix tailTrace_273948
  have hstable : (prefixWord ++ tailWord_273948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273948).length < 2 ^ (prefixWord ++ tailWord_273948).sum := by decide
  have hdescent : baseEnd_273948 < baseStart_273948 := by decide
  rcases family_descends (prefixWord ++ tailWord_273948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273983 : List Nat := [1, 1, 2, 2, 3, 5, 6]
def baseStart_273983 : Nat := 118140960795 + 273983 * 2 ^ 59
def prefixEnd_273983 : Nat := 4983230072969 + 3 ^ 40 * 273983 * 2
def baseEnd_273983 : Nat := 13894811867743878908887

theorem tailTrace_273983 : CollatzResearch.WordTrace tailWord_273983 prefixEnd_273983 13894811867743878908887 := by
  unfold tailWord_273983
  simp only [CollatzResearch.WordTrace]
  refine ⟨9992980966413858416162603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6661987310942572277441735 9992980966413858416162603)
  ·
    refine ⟨14989471449620787624243905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9992980966413858416162603 14989471449620787624243905)
    ·
      refine ⟨11242103587215590718182929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14989471449620787624243905 11242103587215590718182929)
      ·
        refine ⟨8431577690411693038637197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11242103587215590718182929 8431577690411693038637197)
        ·
          refine ⟨3161841633904384889488949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8431577690411693038637197 3161841633904384889488949)
          ·
            refine ⟨296422653178536083389589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3161841633904384889488949 296422653178536083389589)
            ·
              refine ⟨13894811867743878908887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 296422653178536083389589 13894811867743878908887)
              ·
                rfl

theorem cell20_273983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 6].length) (baseStart_273983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273983 prefixEnd_273983 := by exact prefixLift 273983
  have htrace : WordTrace (prefixWord ++ tailWord_273983) baseStart_273983 baseEnd_273983 := by
    simpa [prefixWord, tailWord_273983, baseEnd_273983] using wordTrace_append hprefix tailTrace_273983
  have hstable : (prefixWord ++ tailWord_273983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273983).length < 2 ^ (prefixWord ++ tailWord_273983).sum := by decide
  have hdescent : baseEnd_273983 < baseStart_273983 := by decide
  rcases family_descends (prefixWord ++ tailWord_273983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274007 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 3]
def baseStart_274007 : Nat := 118140960795 + 274007 * 2 ^ 59
def prefixEnd_274007 : Nat := 4983230072969 + 3 ^ 40 * 274007 * 2
def baseEnd_274007 : Nat := 125064261063657493379885

theorem tailTrace_274007 : CollatzResearch.WordTrace tailWord_274007 prefixEnd_274007 125064261063657493379885 := by
  unfold tailWord_274007
  simp only [CollatzResearch.WordTrace]
  refine ⟨9993856318326910515036275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6662570878884607010024183 9993856318326910515036275)
  ·
    refine ⟨14990784477490365772554413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9993856318326910515036275 14990784477490365772554413)
    ·
      refine ⟨5621544179058887164707905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14990784477490365772554413 5621544179058887164707905)
      ·
        refine ⟨4216158134294165373530929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5621544179058887164707905 4216158134294165373530929)
        ·
          refine ⟨3162118600720624030148197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4216158134294165373530929 3162118600720624030148197)
          ·
            refine ⟨592897237635117005652787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3162118600720624030148197 592897237635117005652787)
            ·
              refine ⟨889345856452675508479181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592897237635117005652787 889345856452675508479181)
              ·
                refine ⟨333504696169753315679693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 889345856452675508479181 333504696169753315679693)
                ·
                  refine ⟨125064261063657493379885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333504696169753315679693 125064261063657493379885)
                  ·
                    rfl

theorem cell20_274007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 3].length) (baseStart_274007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274007 prefixEnd_274007 := by exact prefixLift 274007
  have htrace : WordTrace (prefixWord ++ tailWord_274007) baseStart_274007 baseEnd_274007 := by
    simpa [prefixWord, tailWord_274007, baseEnd_274007] using wordTrace_append hprefix tailTrace_274007
  have hstable : (prefixWord ++ tailWord_274007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274007).length < 2 ^ (prefixWord ++ tailWord_274007).sum := by decide
  have hdescent : baseEnd_274007 < baseStart_274007 := by decide
  rcases family_descends (prefixWord ++ tailWord_274007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274021 : List Nat := [1, 3, 1, 3, 3, 1, 2, 6]
def baseStart_274021 : Nat := 118140960795 + 274021 * 2 ^ 59
def prefixEnd_274021 : Nat := 4983230072969 + 3 ^ 40 * 274021 * 2
def baseEnd_274021 : Nat := 41690217015045222304387

theorem tailTrace_274021 : CollatzResearch.WordTrace tailWord_274021 prefixEnd_274021 41690217015045222304387 := by
  unfold tailWord_274021
  simp only [CollatzResearch.WordTrace]
  refine ⟨9994366940276190906045917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6662911293517460604030611 9994366940276190906045917)
  ·
    refine ⟨3747887602603571589767219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9994366940276190906045917 3747887602603571589767219)
    ·
      refine ⟨5621831403905357384650829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3747887602603571589767219 5621831403905357384650829)
      ·
        refine ⟨2108186776464509019244061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5621831403905357384650829 2108186776464509019244061)
        ·
          refine ⟨790570041174190882216523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2108186776464509019244061 790570041174190882216523)
          ·
            refine ⟨1185855061761286323324785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790570041174190882216523 1185855061761286323324785)
            ·
              refine ⟨889391296320964742493589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1185855061761286323324785 889391296320964742493589)
              ·
                refine ⟨41690217015045222304387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 889391296320964742493589 41690217015045222304387)
                ·
                  rfl

theorem cell20_274021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_274021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274021 prefixEnd_274021 := by exact prefixLift 274021
  have htrace : WordTrace (prefixWord ++ tailWord_274021) baseStart_274021 baseEnd_274021 := by
    simpa [prefixWord, tailWord_274021, baseEnd_274021] using wordTrace_append hprefix tailTrace_274021
  have hstable : (prefixWord ++ tailWord_274021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274021).length < 2 ^ (prefixWord ++ tailWord_274021).sum := by decide
  have hdescent : baseEnd_274021 < baseStart_274021 := by decide
  rcases family_descends (prefixWord ++ tailWord_274021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274045 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 3]
def baseStart_274045 : Nat := 118140960795 + 274045 * 2 ^ 59
def prefixEnd_274045 : Nat := 4983230072969 + 3 ^ 40 * 274045 * 2
def baseEnd_274045 : Nat := 125081605299098250113063

theorem tailTrace_274045 : CollatzResearch.WordTrace tailWord_274045 prefixEnd_274045 125081605299098250113063 := by
  unfold tailWord_274045
  simp only [CollatzResearch.WordTrace]
  refine ⟨9995242292189243004919589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6663494861459495336613059 9995242292189243004919589)
  ·
    refine ⟨1874107929785483063422423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9995242292189243004919589 1874107929785483063422423)
    ·
      refine ⟨2811161894678224595133635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1874107929785483063422423 2811161894678224595133635)
      ·
        refine ⟨4216742842017336892700453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2811161894678224595133635 4216742842017336892700453)
        ·
          refine ⟨790639282878250667381335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4216742842017336892700453 790639282878250667381335)
          ·
            refine ⟨1185958924317376001072003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790639282878250667381335 1185958924317376001072003)
            ·
              refine ⟨1778938386476064001608005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185958924317376001072003 1778938386476064001608005)
              ·
                refine ⟨333550947464262000301501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1778938386476064001608005 333550947464262000301501)
                ·
                  refine ⟨125081605299098250113063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333550947464262000301501 125081605299098250113063)
                  ·
                    rfl

theorem cell20_274045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_274045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274045 prefixEnd_274045 := by exact prefixLift 274045
  have htrace : WordTrace (prefixWord ++ tailWord_274045) baseStart_274045 baseEnd_274045 := by
    simpa [prefixWord, tailWord_274045, baseEnd_274045] using wordTrace_append hprefix tailTrace_274045
  have hstable : (prefixWord ++ tailWord_274045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274045).length < 2 ^ (prefixWord ++ tailWord_274045).sum := by decide
  have hdescent : baseEnd_274045 < baseStart_274045 := by decide
  rcases family_descends (prefixWord ++ tailWord_274045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274156 : List Nat := [2, 2, 1, 1, 2, 2, 10]
def baseStart_274156 : Nat := 118140960795 + 274156 * 2 ^ 59
def prefixEnd_274156 : Nat := 4983230072969 + 3 ^ 40 * 274156 * 2
def baseEnd_274156 : Nat := 13903585413741688601401

theorem tailTrace_274156 : CollatzResearch.WordTrace tailWord_274156 prefixEnd_274156 13903585413741688601401 := by
  unfold tailWord_274156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4999645397393554481105161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6666193863191405974806881 4999645397393554481105161)
  ·
    refine ⟨3749734048045165860828871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4999645397393554481105161 3749734048045165860828871)
    ·
      refine ⟨5624601072067748791243307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3749734048045165860828871 5624601072067748791243307)
      ·
        refine ⟨8436901608101623186864961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5624601072067748791243307 8436901608101623186864961)
        ·
          refine ⟨6327676206076217390148721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8436901608101623186864961 6327676206076217390148721)
          ·
            refine ⟨4745757154557163042611541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6327676206076217390148721 4745757154557163042611541)
            ·
              refine ⟨13903585413741688601401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4745757154557163042611541 13903585413741688601401)
              ·
                rfl

theorem cell20_274156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 10].length) (baseStart_274156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274156 prefixEnd_274156 := by exact prefixLift 274156
  have htrace : WordTrace (prefixWord ++ tailWord_274156) baseStart_274156 baseEnd_274156 := by
    simpa [prefixWord, tailWord_274156, baseEnd_274156] using wordTrace_append hprefix tailTrace_274156
  have hstable : (prefixWord ++ tailWord_274156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274156).length < 2 ^ (prefixWord ++ tailWord_274156).sum := by decide
  have hdescent : baseEnd_274156 < baseStart_274156 := by decide
  rcases family_descends (prefixWord ++ tailWord_274156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274162 : List Nat := [3, 2, 1, 3, 1, 1, 5, 2, 2]
def baseStart_274162 : Nat := 118140960795 + 274162 * 2 ^ 59
def prefixEnd_274162 : Nat := 4983230072969 + 3 ^ 40 * 274162 * 2
def baseEnd_274162 : Nat := 125135007287165843212585

theorem tailTrace_274162 : CollatzResearch.WordTrace tailWord_274162 prefixEnd_274162 125135007287165843212585 := by
  unfold tailWord_274162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2499877408191342996732185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6666339755176914657952493 2499877408191342996732185)
  ·
    refine ⟨1874908056143507247549139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2499877408191342996732185 1874908056143507247549139)
    ·
      refine ⟨2812362084215260871323709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1874908056143507247549139 2812362084215260871323709)
      ·
        refine ⟨1054635781580722826746391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2812362084215260871323709 1054635781580722826746391)
        ·
          refine ⟨1581953672371084240119587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054635781580722826746391 1581953672371084240119587)
          ·
            refine ⟨2372930508556626360179381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581953672371084240119587 2372930508556626360179381)
            ·
              refine ⟨222462235177183721266817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2372930508556626360179381 222462235177183721266817)
              ·
                refine ⟨166846676382887790950113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222462235177183721266817 166846676382887790950113)
                ·
                  refine ⟨125135007287165843212585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166846676382887790950113 125135007287165843212585)
                  ·
                    rfl

theorem cell20_274162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_274162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274162 prefixEnd_274162 := by exact prefixLift 274162
  have htrace : WordTrace (prefixWord ++ tailWord_274162) baseStart_274162 baseEnd_274162 := by
    simpa [prefixWord, tailWord_274162, baseEnd_274162] using wordTrace_append hprefix tailTrace_274162
  have hstable : (prefixWord ++ tailWord_274162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274162).length < 2 ^ (prefixWord ++ tailWord_274162).sum := by decide
  have hdescent : baseEnd_274162 < baseStart_274162 := by decide
  rcases family_descends (prefixWord ++ tailWord_274162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274187 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_274187 : Nat := 118140960795 + 274187 * 2 ^ 59
def prefixEnd_274187 : Nat := 4983230072969 + 3 ^ 40 * 274187 * 2
def baseEnd_274187 : Nat := 125146417968376867379149

theorem tailTrace_274187 : CollatzResearch.WordTrace tailWord_274187 prefixEnd_274187 125146417968376867379149 := by
  unfold tailWord_274187
  simp only [CollatzResearch.WordTrace]
  refine ⟨10000421457674801256588815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6666947638449867504392543 10000421457674801256588815)
  ·
    refine ⟨15000632186512201884883223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10000421457674801256588815 15000632186512201884883223)
    ·
      refine ⟨22500948279768302827324835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15000632186512201884883223 22500948279768302827324835)
      ·
        refine ⟨33751422419652454240987253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22500948279768302827324835 33751422419652454240987253)
        ·
          refine ⟨3164195851842417585092555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33751422419652454240987253 3164195851842417585092555)
          ·
            refine ⟨4746293777763626377638833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3164195851842417585092555 4746293777763626377638833)
            ·
              refine ⟨3559720333322719783229125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4746293777763626377638833 3559720333322719783229125)
              ·
                refine ⟨667447562498009959355461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3559720333322719783229125 667447562498009959355461)
                ·
                  refine ⟨125146417968376867379149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667447562498009959355461 125146417968376867379149)
                  ·
                    rfl

theorem cell20_274187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_274187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274187 prefixEnd_274187 := by exact prefixLift 274187
  have htrace : WordTrace (prefixWord ++ tailWord_274187) baseStart_274187 baseEnd_274187 := by
    simpa [prefixWord, tailWord_274187, baseEnd_274187] using wordTrace_append hprefix tailTrace_274187
  have hstable : (prefixWord ++ tailWord_274187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274187).length < 2 ^ (prefixWord ++ tailWord_274187).sum := by decide
  have hdescent : baseEnd_274187 < baseStart_274187 := by decide
  rcases family_descends (prefixWord ++ tailWord_274187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274228 : List Nat := [2, 5, 1, 1, 2, 1, 3, 5]
def baseStart_274228 : Nat := 118140960795 + 274228 * 2 ^ 59
def prefixEnd_274228 : Nat := 4983230072969 + 3 ^ 40 * 274228 * 2
def baseEnd_274228 : Nat := 41721710495187649004105

theorem tailTrace_274228 : CollatzResearch.WordTrace tailWord_274228 prefixEnd_274228 41721710495187649004105 := by
  unfold tailWord_274228
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000958425263132629415669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6667944567017510172554225 5000958425263132629415669)
  ·
    refine ⟨468839852368418684007719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5000958425263132629415669 468839852368418684007719)
    ·
      refine ⟨703259778552628026011579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 468839852368418684007719 703259778552628026011579)
      ·
        refine ⟨1054889667828942039017369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703259778552628026011579 1054889667828942039017369)
        ·
          refine ⟨791167250871706529263027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1054889667828942039017369 791167250871706529263027)
          ·
            refine ⟨1186750876307559793894541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791167250871706529263027 1186750876307559793894541)
            ·
              refine ⟨445031578615334922710453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1186750876307559793894541 445031578615334922710453)
              ·
                refine ⟨41721710495187649004105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 445031578615334922710453 41721710495187649004105)
                ·
                  rfl

theorem cell20_274228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_274228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274228 prefixEnd_274228 := by exact prefixLift 274228
  have htrace : WordTrace (prefixWord ++ tailWord_274228) baseStart_274228 baseEnd_274228 := by
    simpa [prefixWord, tailWord_274228, baseEnd_274228] using wordTrace_append hprefix tailTrace_274228
  have hstable : (prefixWord ++ tailWord_274228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274228).length < 2 ^ (prefixWord ++ tailWord_274228).sum := by decide
  have hdescent : baseEnd_274228 < baseStart_274228 := by decide
  rcases family_descends (prefixWord ++ tailWord_274228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274249 : List Nat := [1, 2, 1, 1, 2, 4, 5, 4]
def baseStart_274249 : Nat := 118140960795 + 274249 * 2 ^ 59
def prefixEnd_274249 : Nat := 4983230072969 + 3 ^ 40 * 274249 * 2
def baseEnd_274249 : Nat := 41724905485926735770743

theorem tailTrace_274249 : CollatzResearch.WordTrace tailWord_274249 prefixEnd_274249 41724905485926735770743 := by
  unfold tailWord_274249
  simp only [CollatzResearch.WordTrace]
  refine ⟨10002682783450185845345801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6668455188966790563563867 10002682783450185845345801)
  ·
    refine ⟨7502012087587639384009351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10002682783450185845345801 7502012087587639384009351)
    ·
      refine ⟨11253018131381459076014027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7502012087587639384009351 11253018131381459076014027)
      ·
        refine ⟨16879527197072188614021041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11253018131381459076014027 16879527197072188614021041)
        ·
          refine ⟨12659645397804141460515781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16879527197072188614021041 12659645397804141460515781)
          ·
            refine ⟨2373683512088276523846709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12659645397804141460515781 2373683512088276523846709)
            ·
              refine ⟨222532829258275924110629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2373683512088276523846709 222532829258275924110629)
              ·
                refine ⟨41724905485926735770743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 222532829258275924110629 41724905485926735770743)
                ·
                  rfl

theorem cell20_274249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 4].length) (baseStart_274249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274249 prefixEnd_274249 := by exact prefixLift 274249
  have htrace : WordTrace (prefixWord ++ tailWord_274249) baseStart_274249 baseEnd_274249 := by
    simpa [prefixWord, tailWord_274249, baseEnd_274249] using wordTrace_append hprefix tailTrace_274249
  have hstable : (prefixWord ++ tailWord_274249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274249).length < 2 ^ (prefixWord ++ tailWord_274249).sum := by decide
  have hdescent : baseEnd_274249 < baseStart_274249 := by decide
  rcases family_descends (prefixWord ++ tailWord_274249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274280 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_274280 : Nat := 118140960795 + 274280 * 2 ^ 59
def prefixEnd_274280 : Nat := 4983230072969 + 3 ^ 40 * 274280 * 2
def baseEnd_274280 : Nat := 125188865702481877278769

theorem tailTrace_274280 : CollatzResearch.WordTrace tailWord_274280 prefixEnd_274280 125188865702481877278769 := by
  unfold tailWord_274280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5001906723168939069862147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6669208964225252093149529 5001906723168939069862147)
  ·
    refine ⟨7502860084753408604793221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5001906723168939069862147 7502860084753408604793221)
    ·
      refine ⟨1406786265891264113398729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7502860084753408604793221 1406786265891264113398729)
      ·
        refine ⟨1055089699418448085049047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1406786265891264113398729 1055089699418448085049047)
        ·
          refine ⟨1582634549127672127573571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055089699418448085049047 1582634549127672127573571)
          ·
            refine ⟨2373951823691508191360357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582634549127672127573571 2373951823691508191360357)
            ·
              refine ⟨445115966942157785880067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2373951823691508191360357 445115966942157785880067)
              ·
                refine ⟨667673950413236678820101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445115966942157785880067 667673950413236678820101)
                ·
                  refine ⟨125188865702481877278769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667673950413236678820101 125188865702481877278769)
                  ·
                    rfl

theorem cell20_274280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_274280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274280 prefixEnd_274280 := by exact prefixLift 274280
  have htrace : WordTrace (prefixWord ++ tailWord_274280) baseStart_274280 baseEnd_274280 := by
    simpa [prefixWord, tailWord_274280, baseEnd_274280] using wordTrace_append hprefix tailTrace_274280
  have hstable : (prefixWord ++ tailWord_274280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274280).length < 2 ^ (prefixWord ++ tailWord_274280).sum := by decide
  have hdescent : baseEnd_274280 < baseStart_274280 := by decide
  rcases family_descends (prefixWord ++ tailWord_274280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274335 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 4]
def baseStart_274335 : Nat := 118140960795 + 274335 * 2 ^ 59
def prefixEnd_274335 : Nat := 4983230072969 + 3 ^ 40 * 274335 * 2
def baseEnd_274335 : Nat := 125213969201146130445211

theorem tailTrace_274335 : CollatzResearch.WordTrace tailWord_274335 prefixEnd_274335 125213969201146130445211 := by
  unfold tailWord_274335
  simp only [CollatzResearch.WordTrace]
  refine ⟨10005819461138622532976459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6670546307425748355317639 10005819461138622532976459)
  ·
    refine ⟨15008729191707933799464689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10005819461138622532976459 15008729191707933799464689)
    ·
      refine ⟨11256546893780950349598517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15008729191707933799464689 11256546893780950349598517)
      ·
        refine ⟨1055301271291964095274861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11256546893780950349598517 1055301271291964095274861)
        ·
          refine ⟨395737976734486535728073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1055301271291964095274861 395737976734486535728073)
          ·
            refine ⟨296803482550864901796055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395737976734486535728073 296803482550864901796055)
            ·
              refine ⟨445205223826297352694083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296803482550864901796055 445205223826297352694083)
              ·
                refine ⟨667807835739446029041125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445205223826297352694083 667807835739446029041125)
                ·
                  refine ⟨125213969201146130445211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667807835739446029041125 125213969201146130445211)
                  ·
                    rfl

theorem cell20_274335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 4].length) (baseStart_274335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274335 prefixEnd_274335 := by exact prefixLift 274335
  have htrace : WordTrace (prefixWord ++ tailWord_274335) baseStart_274335 baseEnd_274335 := by
    simpa [prefixWord, tailWord_274335, baseEnd_274335] using wordTrace_append hprefix tailTrace_274335
  have hstable : (prefixWord ++ tailWord_274335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274335).length < 2 ^ (prefixWord ++ tailWord_274335).sum := by decide
  have hdescent : baseEnd_274335 < baseStart_274335 := by decide
  rcases family_descends (prefixWord ++ tailWord_274335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274386 : List Nat := [3, 2, 2, 3, 3, 1, 2, 2, 2]
def baseStart_274386 : Nat := 118140960795 + 274386 * 2 ^ 59
def prefixEnd_274386 : Nat := 4983230072969 + 3 ^ 40 * 274386 * 2
def baseEnd_274386 : Nat := 125237246990816619745003

theorem tailTrace_274386 : CollatzResearch.WordTrace tailWord_274386 prefixEnd_274386 125237246990816619745003 := by
  unfold tailWord_274386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2501919895988464560770753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6671786389302572162055341 2501919895988464560770753)
  ·
    refine ⟨1876439921991348420578065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2501919895988464560770753 1876439921991348420578065)
    ·
      refine ⟨1407329941493511315433549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1876439921991348420578065 1407329941493511315433549)
      ·
        refine ⟨527748728060066743287581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1407329941493511315433549 527748728060066743287581)
        ·
          refine ⟨197905773022525028732843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 527748728060066743287581 197905773022525028732843)
          ·
            refine ⟨296858659533787543099265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197905773022525028732843 296858659533787543099265)
            ·
              refine ⟨222643994650340657324449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296858659533787543099265 222643994650340657324449)
              ·
                refine ⟨166982995987755492993337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222643994650340657324449 166982995987755492993337)
                ·
                  refine ⟨125237246990816619745003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166982995987755492993337 125237246990816619745003)
                  ·
                    rfl

theorem cell20_274386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_274386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274386 prefixEnd_274386 := by exact prefixLift 274386
  have htrace : WordTrace (prefixWord ++ tailWord_274386) baseStart_274386 baseEnd_274386 := by
    simpa [prefixWord, tailWord_274386, baseEnd_274386] using wordTrace_append hprefix tailTrace_274386
  have hstable : (prefixWord ++ tailWord_274386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274386).length < 2 ^ (prefixWord ++ tailWord_274386).sum := by decide
  have hdescent : baseEnd_274386 < baseStart_274386 := by decide
  rcases family_descends (prefixWord ++ tailWord_274386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274397 : List Nat := [1, 4, 3, 1, 4, 1, 1, 5]
def baseStart_274397 : Nat := 118140960795 + 274397 * 2 ^ 59
def prefixEnd_274397 : Nat := 4983230072969 + 3 ^ 40 * 274397 * 2
def baseEnd_274397 : Nat := 41747422563516490126097

theorem tailTrace_274397 : CollatzResearch.WordTrace tailWord_274397 prefixEnd_274397 41747422563516490126097 := by
  unfold tailWord_274397
  simp only [CollatzResearch.WordTrace]
  refine ⟨10008080786914007121733445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6672053857942671414488963 10008080786914007121733445)
  ·
    refine ⟨1876515147546376335325021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10008080786914007121733445 1876515147546376335325021)
    ·
      refine ⟨703693180329891125746883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1876515147546376335325021 703693180329891125746883)
      ·
        refine ⟨1055539770494836688620325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703693180329891125746883 1055539770494836688620325)
        ·
          refine ⟨197913706967781879116311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1055539770494836688620325 197913706967781879116311)
          ·
            refine ⟨296870560451672818674467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197913706967781879116311 296870560451672818674467)
            ·
              refine ⟨445305840677509228011701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296870560451672818674467 445305840677509228011701)
              ·
                refine ⟨41747422563516490126097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 445305840677509228011701 41747422563516490126097)
                ·
                  rfl

theorem cell20_274397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 5].length) (baseStart_274397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274397 prefixEnd_274397 := by exact prefixLift 274397
  have htrace : WordTrace (prefixWord ++ tailWord_274397) baseStart_274397 baseEnd_274397 := by
    simpa [prefixWord, tailWord_274397, baseEnd_274397] using wordTrace_append hprefix tailTrace_274397
  have hstable : (prefixWord ++ tailWord_274397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274397).length < 2 ^ (prefixWord ++ tailWord_274397).sum := by decide
  have hdescent : baseEnd_274397 < baseStart_274397 := by decide
  rcases family_descends (prefixWord ++ tailWord_274397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274415 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_274415 : Nat := 118140960795 + 274415 * 2 ^ 59
def prefixEnd_274415 : Nat := 4983230072969 + 3 ^ 40 * 274415 * 2
def baseEnd_274415 : Nat := 125250483381021407778217

theorem tailTrace_274415 : CollatzResearch.WordTrace tailWord_274415 prefixEnd_274415 125250483381021407778217 := by
  unfold tailWord_274415
  simp only [CollatzResearch.WordTrace]
  refine ⟨10008737300848796195888699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6672491533899197463925799 10008737300848796195888699)
  ·
    refine ⟨15013105951273194293833049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10008737300848796195888699 15013105951273194293833049)
    ·
      refine ⟨11259829463454895720374787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15013105951273194293833049 11259829463454895720374787)
      ·
        refine ⟨16889744195182343580562181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11259829463454895720374787 16889744195182343580562181)
        ·
          refine ⟨3166827036596689421355409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16889744195182343580562181 3166827036596689421355409)
          ·
            refine ⟨2375120277447517066016557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166827036596689421355409 2375120277447517066016557)
            ·
              refine ⟨890670104042818899756209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2375120277447517066016557 890670104042818899756209)
              ·
                refine ⟨668002578032114174817157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890670104042818899756209 668002578032114174817157)
                ·
                  refine ⟨125250483381021407778217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668002578032114174817157 125250483381021407778217)
                  ·
                    rfl

theorem cell20_274415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_274415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274415 prefixEnd_274415 := by exact prefixLift 274415
  have htrace : WordTrace (prefixWord ++ tailWord_274415) baseStart_274415 baseEnd_274415 := by
    simpa [prefixWord, tailWord_274415, baseEnd_274415] using wordTrace_append hprefix tailTrace_274415
  have hstable : (prefixWord ++ tailWord_274415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274415).length < 2 ^ (prefixWord ++ tailWord_274415).sum := by decide
  have hdescent : baseEnd_274415 < baseStart_274415 := by decide
  rcases family_descends (prefixWord ++ tailWord_274415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274438 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_274438 : Nat := 118140960795 + 274438 * 2 ^ 59
def prefixEnd_274438 : Nat := 4983230072969 + 3 ^ 40 * 274438 * 2
def baseEnd_274438 : Nat := 125260981207735550011457

theorem tailTrace_274438 : CollatzResearch.WordTrace tailWord_274438 prefixEnd_274438 125260981207735550011457 := by
  unfold tailWord_274438
  simp only [CollatzResearch.WordTrace]
  refine ⟨312799255617670972624249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6673050786510314082650645 312799255617670972624249)
  ·
    refine ⟨234599441713253229468187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 312799255617670972624249 234599441713253229468187)
    ·
      refine ⟨351899162569879844202281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234599441713253229468187 351899162569879844202281)
      ·
        refine ⟨263924371927409883151711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351899162569879844202281 263924371927409883151711)
        ·
          refine ⟨395886557891114824727567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263924371927409883151711 395886557891114824727567)
          ·
            refine ⟨593829836836672237091351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395886557891114824727567 593829836836672237091351)
            ·
              refine ⟨890744755255008355637027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593829836836672237091351 890744755255008355637027)
              ·
                refine ⟨1336117132882512533455541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890744755255008355637027 1336117132882512533455541)
                ·
                  refine ⟨125260981207735550011457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1336117132882512533455541 125260981207735550011457)
                  ·
                    rfl

theorem cell20_274438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_274438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274438 prefixEnd_274438 := by exact prefixLift 274438
  have htrace : WordTrace (prefixWord ++ tailWord_274438) baseStart_274438 baseEnd_274438 := by
    simpa [prefixWord, tailWord_274438, baseEnd_274438] using wordTrace_append hprefix tailTrace_274438
  have hstable : (prefixWord ++ tailWord_274438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274438).length < 2 ^ (prefixWord ++ tailWord_274438).sum := by decide
  have hdescent : baseEnd_274438 < baseStart_274438 := by decide
  rcases family_descends (prefixWord ++ tailWord_274438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274442 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_274442 : Nat := 118140960795 + 274442 * 2 ^ 59
def prefixEnd_274442 : Nat := 4983230072969 + 3 ^ 40 * 274442 * 2
def baseEnd_274442 : Nat := 125262806916729313878107

theorem tailTrace_274442 : CollatzResearch.WordTrace tailWord_274442 prefixEnd_274442 125262806916729313878107 := by
  unfold tailWord_274442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2502430517937744951780395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6673148047833986538081053 2502430517937744951780395)
  ·
    refine ⟨3753645776906617427670593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2502430517937744951780395 3753645776906617427670593)
    ·
      refine ⟨2815234332679963070752945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3753645776906617427670593 2815234332679963070752945)
      ·
        refine ⟨2111425749509972303064709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2815234332679963070752945 2111425749509972303064709)
        ·
          refine ⟨395892328033119806824633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2111425749509972303064709 395892328033119806824633)
          ·
            refine ⟨296919246024839855118475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395892328033119806824633 296919246024839855118475)
            ·
              refine ⟨445378869037259782677713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296919246024839855118475 445378869037259782677713)
              ·
                refine ⟨334034151777944837008285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445378869037259782677713 334034151777944837008285)
                ·
                  refine ⟨125262806916729313878107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334034151777944837008285 125262806916729313878107)
                  ·
                    rfl

theorem cell20_274442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_274442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274442 prefixEnd_274442 := by exact prefixLift 274442
  have htrace : WordTrace (prefixWord ++ tailWord_274442) baseStart_274442 baseEnd_274442 := by
    simpa [prefixWord, tailWord_274442, baseEnd_274442] using wordTrace_append hprefix tailTrace_274442
  have hstable : (prefixWord ++ tailWord_274442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274442).length < 2 ^ (prefixWord ++ tailWord_274442).sum := by decide
  have hdescent : baseEnd_274442 < baseStart_274442 := by decide
  rcases family_descends (prefixWord ++ tailWord_274442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274445 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 4]
def baseStart_274445 : Nat := 118140960795 + 274445 * 2 ^ 59
def prefixEnd_274445 : Nat := 4983230072969 + 3 ^ 40 * 274445 * 2
def baseEnd_274445 : Nat := 125264176198474636778095

theorem tailTrace_274445 : CollatzResearch.WordTrace tailWord_274445 prefixEnd_274445 125264176198474636778095 := by
  unfold tailWord_274445
  simp only [CollatzResearch.WordTrace]
  refine ⟨10009831490740111319480789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6673220993826740879653859 10009831490740111319480789)
  ·
    refine ⟨234605425564221359050331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10009831490740111319480789 234605425564221359050331)
    ·
      refine ⟨351908138346332038575497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234605425564221359050331 351908138346332038575497)
      ·
        refine ⟨263931103759749028931623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351908138346332038575497 263931103759749028931623)
        ·
          refine ⟨395896655639623543397435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263931103759749028931623 395896655639623543397435)
          ·
            refine ⟨593844983459435315096153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395896655639623543397435 593844983459435315096153)
            ·
              refine ⟨445383737594576486322115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593844983459435315096153 445383737594576486322115)
              ·
                refine ⟨668075606391864729483173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445383737594576486322115 668075606391864729483173)
                ·
                  refine ⟨125264176198474636778095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668075606391864729483173 125264176198474636778095)
                  ·
                    rfl

theorem cell20_274445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_274445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274445 prefixEnd_274445 := by exact prefixLift 274445
  have htrace : WordTrace (prefixWord ++ tailWord_274445) baseStart_274445 baseEnd_274445 := by
    simpa [prefixWord, tailWord_274445, baseEnd_274445] using wordTrace_append hprefix tailTrace_274445
  have hstable : (prefixWord ++ tailWord_274445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274445).length < 2 ^ (prefixWord ++ tailWord_274445).sum := by decide
  have hdescent : baseEnd_274445 < baseStart_274445 := by decide
  rcases family_descends (prefixWord ++ tailWord_274445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274446 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_274446 : Nat := 118140960795 + 274446 * 2 ^ 59
def prefixEnd_274446 : Nat := 4983230072969 + 3 ^ 40 * 274446 * 2
def baseEnd_274446 : Nat := 125264632625723077744757

theorem tailTrace_274446 : CollatzResearch.WordTrace tailWord_274446 prefixEnd_274446 125264632625723077744757 := by
  unfold tailWord_274446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251233495467061061283399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6673245309157658993511461 1251233495467061061283399)
  ·
    refine ⟨1876850243200591591925099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1251233495467061061283399 1876850243200591591925099)
    ·
      refine ⟨2815275364800887387887649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1876850243200591591925099 2815275364800887387887649)
      ·
        refine ⟨2111456523600665540915737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2815275364800887387887649 2111456523600665540915737)
        ·
          refine ⟨1583592392700499155686803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2111456523600665540915737 1583592392700499155686803)
          ·
            refine ⟨2375388589050748733530205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583592392700499155686803 2375388589050748733530205)
            ·
              refine ⟨890770720894030775073827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2375388589050748733530205 890770720894030775073827)
              ·
                refine ⟨1336156081341046162610741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890770720894030775073827 1336156081341046162610741)
                ·
                  refine ⟨125264632625723077744757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1336156081341046162610741 125264632625723077744757)
                  ·
                    rfl

theorem cell20_274446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_274446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274446 prefixEnd_274446 := by exact prefixLift 274446
  have htrace : WordTrace (prefixWord ++ tailWord_274446) baseStart_274446 baseEnd_274446 := by
    simpa [prefixWord, tailWord_274446, baseEnd_274446] using wordTrace_append hprefix tailTrace_274446
  have hstable : (prefixWord ++ tailWord_274446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274446).length < 2 ^ (prefixWord ++ tailWord_274446).sum := by decide
  have hdescent : baseEnd_274446 < baseStart_274446 := by decide
  rcases family_descends (prefixWord ++ tailWord_274446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274463 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 3]
def baseStart_274463 : Nat := 118140960795 + 274463 * 2 ^ 59
def prefixEnd_274463 : Nat := 4983230072969 + 3 ^ 40 * 274463 * 2
def baseEnd_274463 : Nat := 125272391888946574178021

theorem tailTrace_274463 : CollatzResearch.WordTrace tailWord_274463 prefixEnd_274463 125272391888946574178021 := by
  unfold tailWord_274463
  simp only [CollatzResearch.WordTrace]
  refine ⟨10010488004674900393636043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6673658669783266929090695 10010488004674900393636043)
  ·
    refine ⟨15015732007012350590454065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10010488004674900393636043 15015732007012350590454065)
    ·
      refine ⟨11261799005259262942840549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15015732007012350590454065 11261799005259262942840549)
      ·
        refine ⟨2111587313486111801782603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11261799005259262942840549 2111587313486111801782603)
        ·
          refine ⟨3167380970229167702673905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111587313486111801782603 3167380970229167702673905)
          ·
            refine ⟨2375535727671875777005429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3167380970229167702673905 2375535727671875777005429)
            ·
              refine ⟨222706474469238354094259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2375535727671875777005429 222706474469238354094259)
              ·
                refine ⟨334059711703857531141389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222706474469238354094259 334059711703857531141389)
                ·
                  refine ⟨125272391888946574178021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334059711703857531141389 125272391888946574178021)
                  ·
                    rfl

theorem cell20_274463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 3].length) (baseStart_274463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274463 prefixEnd_274463 := by exact prefixLift 274463
  have htrace : WordTrace (prefixWord ++ tailWord_274463) baseStart_274463 baseEnd_274463 := by
    simpa [prefixWord, tailWord_274463, baseEnd_274463] using wordTrace_append hprefix tailTrace_274463
  have hstable : (prefixWord ++ tailWord_274463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274463).length < 2 ^ (prefixWord ++ tailWord_274463).sum := by decide
  have hdescent : baseEnd_274463 < baseStart_274463 := by decide
  rcases family_descends (prefixWord ++ tailWord_274463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274494 : List Nat := [4, 2, 1, 3, 2, 2, 6]
def baseStart_274494 : Nat := 118140960795 + 274494 * 2 ^ 59
def prefixEnd_274494 : Nat := 4983230072969 + 3 ^ 40 * 274494 * 2
def baseEnd_274494 : Nat := 13920726792627582682729

theorem tailTrace_274494 : CollatzResearch.WordTrace tailWord_274494 prefixEnd_274494 13920726792627582682729 := by
  unfold tailWord_274494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251452333445324086001817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6674412445041728458676357 1251452333445324086001817)
  ·
    refine ⟨938589250083993064501363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1251452333445324086001817 938589250083993064501363)
    ·
      refine ⟨1407883875125989596752045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 938589250083993064501363 1407883875125989596752045)
      ·
        refine ⟨527956453172246098782017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1407883875125989596752045 527956453172246098782017)
        ·
          refine ⟨395967339879184574086513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527956453172246098782017 395967339879184574086513)
          ·
            refine ⟨296975504909388430564885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395967339879184574086513 296975504909388430564885)
            ·
              refine ⟨13920726792627582682729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 296975504909388430564885 13920726792627582682729)
              ·
                rfl

theorem cell20_274494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 6].length) (baseStart_274494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274494 prefixEnd_274494 := by exact prefixLift 274494
  have htrace : WordTrace (prefixWord ++ tailWord_274494) baseStart_274494 baseEnd_274494 := by
    simpa [prefixWord, tailWord_274494, baseEnd_274494] using wordTrace_append hprefix tailTrace_274494
  have hstable : (prefixWord ++ tailWord_274494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274494).length < 2 ^ (prefixWord ++ tailWord_274494).sum := by decide
  have hdescent : baseEnd_274494 < baseStart_274494 := by decide
  rcases family_descends (prefixWord ++ tailWord_274494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274505 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_274505 : Nat := 118140960795 + 274505 * 2 ^ 59
def prefixEnd_274505 : Nat := 4983230072969 + 3 ^ 40 * 274505 * 2
def baseEnd_274505 : Nat := 125291561833381094777849

theorem tailTrace_274505 : CollatzResearch.WordTrace tailWord_274505 prefixEnd_274505 125291561833381094777849 := by
  unfold tailWord_274505
  simp only [CollatzResearch.WordTrace]
  refine ⟨10012019870522741566664969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6674679913681827711109979 10012019870522741566664969)
  ·
    refine ⟨7509014902892056174998727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10012019870522741566664969 7509014902892056174998727)
    ·
      refine ⟨11263522354338084262498091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7509014902892056174998727 11263522354338084262498091)
      ·
        refine ⟨16895283531507126393747137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11263522354338084262498091 16895283531507126393747137)
        ·
          refine ⟨12671462648630344795310353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16895283531507126393747137 12671462648630344795310353)
          ·
            refine ⟨9503596986472758596482765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12671462648630344795310353 9503596986472758596482765)
            ·
              refine ⟨3563848869927284473681037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9503596986472758596482765 3563848869927284473681037)
              ·
                refine ⟨1336443326222731677630389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3563848869927284473681037 1336443326222731677630389)
                ·
                  refine ⟨125291561833381094777849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1336443326222731677630389 125291561833381094777849)
                  ·
                    rfl

theorem cell20_274505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_274505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274505 prefixEnd_274505 := by exact prefixLift 274505
  have htrace : WordTrace (prefixWord ++ tailWord_274505) baseStart_274505 baseEnd_274505 := by
    simpa [prefixWord, tailWord_274505, baseEnd_274505] using wordTrace_append hprefix tailTrace_274505
  have hstable : (prefixWord ++ tailWord_274505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274505).length < 2 ^ (prefixWord ++ tailWord_274505).sum := by decide
  have hdescent : baseEnd_274505 < baseStart_274505 := by decide
  rcases family_descends (prefixWord ++ tailWord_274505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274508 : List Nat := [2, 2, 1, 3, 1, 1, 2, 6, 2]
def baseStart_274508 : Nat := 118140960795 + 274508 * 2 ^ 59
def prefixEnd_274508 : Nat := 4983230072969 + 3 ^ 40 * 274508 * 2
def baseEnd_274508 : Nat := 125292931115126417677837

theorem tailTrace_274508 : CollatzResearch.WordTrace tailWord_274508 prefixEnd_274508 125292931115126417677837 := by
  unfold tailWord_274508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006064644755936539512089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6674752859674582052682785 5006064644755936539512089)
  ·
    refine ⟨3754548483566952404634067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5006064644755936539512089 3754548483566952404634067)
    ·
      refine ⟨5631822725350428606951101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3754548483566952404634067 5631822725350428606951101)
      ·
        refine ⟨2111933522006410727606663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5631822725350428606951101 2111933522006410727606663)
        ·
          refine ⟨3167900283009616091409995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111933522006410727606663 3167900283009616091409995)
          ·
            refine ⟨4751850424514424137114993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167900283009616091409995 4751850424514424137114993)
            ·
              refine ⟨3563887818385818102836245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4751850424514424137114993 3563887818385818102836245)
              ·
                refine ⟨167057241486835223570449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3563887818385818102836245 167057241486835223570449)
                ·
                  refine ⟨125292931115126417677837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167057241486835223570449 125292931115126417677837)
                  ·
                    rfl

theorem cell20_274508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_274508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274508 prefixEnd_274508 := by exact prefixLift 274508
  have htrace : WordTrace (prefixWord ++ tailWord_274508) baseStart_274508 baseEnd_274508 := by
    simpa [prefixWord, tailWord_274508, baseEnd_274508] using wordTrace_append hprefix tailTrace_274508
  have hstable : (prefixWord ++ tailWord_274508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274508).length < 2 ^ (prefixWord ++ tailWord_274508).sum := by decide
  have hdescent : baseEnd_274508 < baseStart_274508 := by decide
  rcases family_descends (prefixWord ++ tailWord_274508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274522 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_274522 : Nat := 118140960795 + 274522 * 2 ^ 59
def prefixEnd_274522 : Nat := 4983230072969 + 3 ^ 40 * 274522 * 2
def baseEnd_274522 : Nat := 125299321096604591211113

theorem tailTrace_274522 : CollatzResearch.WordTrace tailWord_274522 prefixEnd_274522 125299321096604591211113 := by
  unfold tailWord_274522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503159977865288367508455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6675093274307435646689213 2503159977865288367508455)
  ·
    refine ⟨3754739966797932551262683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2503159977865288367508455 3754739966797932551262683)
    ·
      refine ⟨5632109950196898826894025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3754739966797932551262683 5632109950196898826894025)
      ·
        refine ⟨4224082462647674120170519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5632109950196898826894025 4224082462647674120170519)
        ·
          refine ⟨6336123693971511180255779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224082462647674120170519 6336123693971511180255779)
          ·
            refine ⟨9504185540957266770383669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6336123693971511180255779 9504185540957266770383669)
            ·
              refine ⟨891017394464743759723469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9504185540957266770383669 891017394464743759723469)
              ·
                refine ⟨334131522924278909896301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 891017394464743759723469 334131522924278909896301)
                ·
                  refine ⟨125299321096604591211113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334131522924278909896301 125299321096604591211113)
                  ·
                    rfl

theorem cell20_274522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_274522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274522 prefixEnd_274522 := by exact prefixLift 274522
  have htrace : WordTrace (prefixWord ++ tailWord_274522) baseStart_274522 baseEnd_274522 := by
    simpa [prefixWord, tailWord_274522, baseEnd_274522] using wordTrace_append hprefix tailTrace_274522
  have hstable : (prefixWord ++ tailWord_274522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274522).length < 2 ^ (prefixWord ++ tailWord_274522).sum := by decide
  have hdescent : baseEnd_274522 < baseStart_274522 := by decide
  rcases family_descends (prefixWord ++ tailWord_274522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274563 : List Nat := [1, 1, 1, 3, 3, 3, 4, 2, 2]
def baseStart_274563 : Nat := 118140960795 + 274563 * 2 ^ 59
def prefixEnd_274563 : Nat := 4983230072969 + 3 ^ 40 * 274563 * 2
def baseEnd_274563 : Nat := 125318034613790670844279

theorem tailTrace_274563 : CollatzResearch.WordTrace tailWord_274563 prefixEnd_274563 125318034613790670844279 := by
  unfold tailWord_274563
  simp only [CollatzResearch.WordTrace]
  refine ⟨10014135304312617472276343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6676090202875078314850895 10014135304312617472276343)
  ·
    refine ⟨15021202956468926208414515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10014135304312617472276343 15021202956468926208414515)
    ·
      refine ⟨22531804434703389312621773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15021202956468926208414515 22531804434703389312621773)
      ·
        refine ⟨8449426663013770992233165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22531804434703389312621773 8449426663013770992233165)
        ·
          refine ⟨3168534998630164122087437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8449426663013770992233165 3168534998630164122087437)
          ·
            refine ⟨1188200624486311545782789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3168534998630164122087437 1188200624486311545782789)
            ·
              refine ⟨222787617091183414834273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1188200624486311545782789 222787617091183414834273)
              ·
                refine ⟨167090712818387561125705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222787617091183414834273 167090712818387561125705)
                ·
                  refine ⟨125318034613790670844279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167090712818387561125705 125318034613790670844279)
                  ·
                    rfl

theorem cell20_274563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 2].length) (baseStart_274563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274563 prefixEnd_274563 := by exact prefixLift 274563
  have htrace : WordTrace (prefixWord ++ tailWord_274563) baseStart_274563 baseEnd_274563 := by
    simpa [prefixWord, tailWord_274563, baseEnd_274563] using wordTrace_append hprefix tailTrace_274563
  have hstable : (prefixWord ++ tailWord_274563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274563).length < 2 ^ (prefixWord ++ tailWord_274563).sum := by decide
  have hdescent : baseEnd_274563 < baseStart_274563 := by decide
  rcases family_descends (prefixWord ++ tailWord_274563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274584 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 4]
def baseStart_274584 : Nat := 118140960795 + 274584 * 2 ^ 59
def prefixEnd_274584 : Nat := 4983230072969 + 3 ^ 40 * 274584 * 2
def baseEnd_274584 : Nat := 125327619586007931144193

theorem tailTrace_274584 : CollatzResearch.WordTrace tailWord_274584 prefixEnd_274584 125327619586007931144193 := by
  unfold tailWord_274584
  simp only [CollatzResearch.WordTrace]
  refine ⟨5007450618618269029395403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6676600824824358705860537 5007450618618269029395403)
  ·
    refine ⟨7511175927927403544093105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5007450618618269029395403 7511175927927403544093105)
    ·
      refine ⟨5633381945945552658069829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7511175927927403544093105 5633381945945552658069829)
      ·
        refine ⟨1056259114864791123388093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5633381945945552658069829 1056259114864791123388093)
        ·
          refine ⟨396097168074296671270535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1056259114864791123388093 396097168074296671270535)
          ·
            refine ⟨594145752111445006905803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396097168074296671270535 594145752111445006905803)
            ·
              refine ⟨891218628167167510358705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594145752111445006905803 891218628167167510358705)
              ·
                refine ⟨668413971125375632769029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891218628167167510358705 668413971125375632769029)
                ·
                  refine ⟨125327619586007931144193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668413971125375632769029 125327619586007931144193)
                  ·
                    rfl

theorem cell20_274584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_274584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274584 prefixEnd_274584 := by exact prefixLift 274584
  have htrace : WordTrace (prefixWord ++ tailWord_274584) baseStart_274584 baseEnd_274584 := by
    simpa [prefixWord, tailWord_274584, baseEnd_274584] using wordTrace_append hprefix tailTrace_274584
  have hstable : (prefixWord ++ tailWord_274584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274584).length < 2 ^ (prefixWord ++ tailWord_274584).sum := by decide
  have hdescent : baseEnd_274584 < baseStart_274584 := by decide
  rcases family_descends (prefixWord ++ tailWord_274584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274615 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 3]
def baseStart_274615 : Nat := 118140960795 + 274615 * 2 ^ 59
def prefixEnd_274615 : Nat := 4983230072969 + 3 ^ 40 * 274615 * 2
def baseEnd_274615 : Nat := 125341768830709601110733

theorem tailTrace_274615 : CollatzResearch.WordTrace tailWord_274615 prefixEnd_274615 125341768830709601110733 := by
  unfold tailWord_274615
  simp only [CollatzResearch.WordTrace]
  refine ⟨10016031900124230353169299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6677354600082820235446199 10016031900124230353169299)
  ·
    refine ⟨15024047850186345529753949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10016031900124230353169299 15024047850186345529753949)
    ·
      refine ⟨5634017943819879573657731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15024047850186345529753949 5634017943819879573657731)
      ·
        refine ⟨8451026915729819360486597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5634017943819879573657731 8451026915729819360486597)
        ·
          refine ⟨1584567546699341130091237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8451026915729819360486597 1584567546699341130091237)
          ·
            refine ⟨297106415006126461892107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1584567546699341130091237 297106415006126461892107)
            ·
              refine ⟨445659622509189692838161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297106415006126461892107 445659622509189692838161)
              ·
                refine ⟨334244716881892269628621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445659622509189692838161 334244716881892269628621)
                ·
                  refine ⟨125341768830709601110733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334244716881892269628621 125341768830709601110733)
                  ·
                    rfl

theorem cell20_274615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 3].length) (baseStart_274615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274615 prefixEnd_274615 := by exact prefixLift 274615
  have htrace : WordTrace (prefixWord ++ tailWord_274615) baseStart_274615 baseEnd_274615 := by
    simpa [prefixWord, tailWord_274615, baseEnd_274615] using wordTrace_append hprefix tailTrace_274615
  have hstable : (prefixWord ++ tailWord_274615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274615).length < 2 ^ (prefixWord ++ tailWord_274615).sum := by decide
  have hdescent : baseEnd_274615 < baseStart_274615 := by decide
  rcases family_descends (prefixWord ++ tailWord_274615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274619 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_274619 : Nat := 118140960795 + 274619 * 2 ^ 59
def prefixEnd_274619 : Nat := 4983230072969 + 3 ^ 40 * 274619 * 2
def baseEnd_274619 : Nat := 125343594539703364977383

theorem tailTrace_274619 : CollatzResearch.WordTrace tailWord_274619 prefixEnd_274619 125343594539703364977383 := by
  unfold tailWord_274619
  simp only [CollatzResearch.WordTrace]
  refine ⟨10016177792109739036314911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6677451861406492690876607 10016177792109739036314911)
  ·
    refine ⟨15024266688164608554472367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10016177792109739036314911 15024266688164608554472367)
    ·
      refine ⟨22536400032246912831708551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15024266688164608554472367 22536400032246912831708551)
      ·
        refine ⟨33804600048370369247562827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22536400032246912831708551 33804600048370369247562827)
        ·
          refine ⟨50706900072555553871344241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33804600048370369247562827 50706900072555553871344241)
          ·
            refine ⟨38030175054416665403508181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50706900072555553871344241 38030175054416665403508181)
            ·
              refine ⟨891332227837890595394723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 38030175054416665403508181 891332227837890595394723)
              ·
                refine ⟨1336998341756835893092085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891332227837890595394723 1336998341756835893092085)
                ·
                  refine ⟨125343594539703364977383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1336998341756835893092085 125343594539703364977383)
                  ·
                    rfl

theorem cell20_274619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_274619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274619 prefixEnd_274619 := by exact prefixLift 274619
  have htrace : WordTrace (prefixWord ++ tailWord_274619) baseStart_274619 baseEnd_274619 := by
    simpa [prefixWord, tailWord_274619, baseEnd_274619] using wordTrace_append hprefix tailTrace_274619
  have hstable : (prefixWord ++ tailWord_274619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274619).length < 2 ^ (prefixWord ++ tailWord_274619).sum := by decide
  have hdescent : baseEnd_274619 < baseStart_274619 := by decide
  rcases family_descends (prefixWord ++ tailWord_274619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274646 : List Nat := [5, 2, 1, 2, 1, 2, 1, 6]
def baseStart_274646 : Nat := 118140960795 + 274646 * 2 ^ 59
def prefixEnd_274646 : Nat := 4983230072969 + 3 ^ 40 * 274646 * 2
def baseEnd_274646 : Nat := 41785306025137090359091

theorem tailTrace_274646 : CollatzResearch.WordTrace tailWord_274646 prefixEnd_274646 41785306025137090359091 := by
  unfold tailWord_274646
  simp only [CollatzResearch.WordTrace]
  refine ⟨626072660188245165471737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6678108375341281765031861 626072660188245165471737)
  ·
    refine ⟨469554495141183874103803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 626072660188245165471737 469554495141183874103803)
    ·
      refine ⟨704331742711775811155705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469554495141183874103803 704331742711775811155705)
      ·
        refine ⟨528248807033831858366779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704331742711775811155705 528248807033831858366779)
        ·
          refine ⟨792373210550747787550169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528248807033831858366779 792373210550747787550169)
          ·
            refine ⟨594279907913060840662627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792373210550747787550169 594279907913060840662627)
            ·
              refine ⟨891419861869591260993941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594279907913060840662627 891419861869591260993941)
              ·
                refine ⟨41785306025137090359091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 891419861869591260993941 41785306025137090359091)
                ·
                  rfl

theorem cell20_274646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_274646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274646 prefixEnd_274646 := by exact prefixLift 274646
  have htrace : WordTrace (prefixWord ++ tailWord_274646) baseStart_274646 baseEnd_274646 := by
    simpa [prefixWord, tailWord_274646, baseEnd_274646] using wordTrace_append hprefix tailTrace_274646
  have hstable : (prefixWord ++ tailWord_274646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274646).length < 2 ^ (prefixWord ++ tailWord_274646).sum := by decide
  have hdescent : baseEnd_274646 < baseStart_274646 := by decide
  rcases family_descends (prefixWord ++ tailWord_274646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274652 : List Nat := [2, 2, 5, 2, 2, 1, 1, 3, 2]
def baseStart_274652 : Nat := 118140960795 + 274652 * 2 ^ 59
def prefixEnd_274652 : Nat := 4983230072969 + 3 ^ 40 * 274652 * 2
def baseEnd_274652 : Nat := 125358656638901916877249

theorem tailTrace_274652 : CollatzResearch.WordTrace tailWord_274652 prefixEnd_274652 125358656638901916877249 := by
  unfold tailWord_274652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5008690700495092836133105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6678254267326790448177473 5008690700495092836133105)
  ·
    refine ⟨3756518025371319627099829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5008690700495092836133105 3756518025371319627099829)
    ·
      refine ⟨352173564878561215040609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3756518025371319627099829 352173564878561215040609)
      ·
        refine ⟨264130173658920911280457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352173564878561215040609 264130173658920911280457)
        ·
          refine ⟨198097630244190683460343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264130173658920911280457 198097630244190683460343)
          ·
            refine ⟨297146445366286025190515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198097630244190683460343 297146445366286025190515)
            ·
              refine ⟨445719668049429037785773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297146445366286025190515 445719668049429037785773)
              ·
                refine ⟨167144875518535889169665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 445719668049429037785773 167144875518535889169665)
                ·
                  refine ⟨125358656638901916877249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167144875518535889169665 125358656638901916877249)
                  ·
                    rfl

theorem cell20_274652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_274652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274652 prefixEnd_274652 := by exact prefixLift 274652
  have htrace : WordTrace (prefixWord ++ tailWord_274652) baseStart_274652 baseEnd_274652 := by
    simpa [prefixWord, tailWord_274652, baseEnd_274652] using wordTrace_append hprefix tailTrace_274652
  have hstable : (prefixWord ++ tailWord_274652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274652).length < 2 ^ (prefixWord ++ tailWord_274652).sum := by decide
  have hdescent : baseEnd_274652 < baseStart_274652 := by decide
  rcases family_descends (prefixWord ++ tailWord_274652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274657 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_274657 : Nat := 118140960795 + 274657 * 2 ^ 59
def prefixEnd_274657 : Nat := 4983230072969 + 3 ^ 40 * 274657 * 2
def baseEnd_274657 : Nat := 125360938775144121710561

theorem tailTrace_274657 : CollatzResearch.WordTrace tailWord_274657 prefixEnd_274657 125360938775144121710561 := by
  unfold tailWord_274657
  simp only [CollatzResearch.WordTrace]
  refine ⟨10017563765972071526198225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6678375843981381017465483 10017563765972071526198225)
  ·
    refine ⟨7513172824479053644648669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10017563765972071526198225 7513172824479053644648669)
    ·
      refine ⟨2817439809179645116743251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7513172824479053644648669 2817439809179645116743251)
      ·
        refine ⟨4226159713769467675114877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2817439809179645116743251 4226159713769467675114877)
        ·
          refine ⟨1584809892663550378168079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4226159713769467675114877 1584809892663550378168079)
          ·
            refine ⟨2377214838995325567252119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584809892663550378168079 2377214838995325567252119)
            ·
              refine ⟨3565822258492988350878179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377214838995325567252119 3565822258492988350878179)
              ·
                refine ⟨5348733387739482526317269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565822258492988350878179 5348733387739482526317269)
                ·
                  refine ⟨125360938775144121710561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5348733387739482526317269 125360938775144121710561)
                  ·
                    rfl

theorem cell20_274657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_274657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274657 prefixEnd_274657 := by exact prefixLift 274657
  have htrace : WordTrace (prefixWord ++ tailWord_274657) baseStart_274657 baseEnd_274657 := by
    simpa [prefixWord, tailWord_274657, baseEnd_274657] using wordTrace_append hprefix tailTrace_274657
  have hstable : (prefixWord ++ tailWord_274657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274657).length < 2 ^ (prefixWord ++ tailWord_274657).sum := by decide
  have hdescent : baseEnd_274657 < baseStart_274657 := by decide
  rcases family_descends (prefixWord ++ tailWord_274657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274674 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_274674 : Nat := 118140960795 + 274674 * 2 ^ 59
def prefixEnd_274674 : Nat := 4983230072969 + 3 ^ 40 * 274674 * 2
def baseEnd_274674 : Nat := 125368698038367618143825

theorem tailTrace_274674 : CollatzResearch.WordTrace tailWord_274674 prefixEnd_274674 125368698038367618143825 := by
  unfold tailWord_274674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2504545951727620857391769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6678789204606988953044717 2504545951727620857391769)
  ·
    refine ⟨1878409463795715643043827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2504545951727620857391769 1878409463795715643043827)
    ·
      refine ⟨2817614195693573464565741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1878409463795715643043827 2817614195693573464565741)
      ·
        refine ⟨1056605323385090049212153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2817614195693573464565741 1056605323385090049212153)
        ·
          refine ⟨792453992538817536909115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1056605323385090049212153 792453992538817536909115)
          ·
            refine ⟨1188680988808226305363673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792453992538817536909115 1188680988808226305363673)
            ·
              refine ⟨891510741606169729022755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188680988808226305363673 891510741606169729022755)
              ·
                refine ⟨1337266112409254593534133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891510741606169729022755 1337266112409254593534133)
                ·
                  refine ⟨125368698038367618143825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1337266112409254593534133 125368698038367618143825)
                  ·
                    rfl

theorem cell20_274674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_274674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274674 prefixEnd_274674 := by exact prefixLift 274674
  have htrace : WordTrace (prefixWord ++ tailWord_274674) baseStart_274674 baseEnd_274674 := by
    simpa [prefixWord, tailWord_274674, baseEnd_274674] using wordTrace_append hprefix tailTrace_274674
  have hstable : (prefixWord ++ tailWord_274674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274674).length < 2 ^ (prefixWord ++ tailWord_274674).sum := by decide
  have hdescent : baseEnd_274674 < baseStart_274674 := by decide
  rcases family_descends (prefixWord ++ tailWord_274674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274778 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_274778 : Nat := 118140960795 + 274778 * 2 ^ 59
def prefixEnd_274778 : Nat := 4983230072969 + 3 ^ 40 * 274778 * 2
def baseEnd_274778 : Nat := 125416166472205478676733

theorem tailTrace_274778 : CollatzResearch.WordTrace tailWord_274778 prefixEnd_274778 125416166472205478676733 := by
  unfold tailWord_274778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505494249633427297838247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6681317999022472794235325 2505494249633427297838247)
  ·
    refine ⟨3758241374450140946757371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2505494249633427297838247 3758241374450140946757371)
    ·
      refine ⟨5637362061675211420136057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3758241374450140946757371 5637362061675211420136057)
      ·
        refine ⟨4228021546256408565102043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5637362061675211420136057 4228021546256408565102043)
        ·
          refine ⟨6342032319384612847653065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228021546256408565102043 6342032319384612847653065)
          ·
            refine ⟨4756524239538459635739799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6342032319384612847653065 4756524239538459635739799)
            ·
              refine ⟨7134786359307689453609699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4756524239538459635739799 7134786359307689453609699)
              ·
                refine ⟨10702179538961534180414549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7134786359307689453609699 10702179538961534180414549)
                ·
                  refine ⟨125416166472205478676733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10702179538961534180414549 125416166472205478676733)
                  ·
                    rfl

theorem cell20_274778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_274778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274778 prefixEnd_274778 := by exact prefixLift 274778
  have htrace : WordTrace (prefixWord ++ tailWord_274778) baseStart_274778 baseEnd_274778 := by
    simpa [prefixWord, tailWord_274778, baseEnd_274778] using wordTrace_append hprefix tailTrace_274778
  have hstable : (prefixWord ++ tailWord_274778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274778).length < 2 ^ (prefixWord ++ tailWord_274778).sum := by decide
  have hdescent : baseEnd_274778 < baseStart_274778 := by decide
  rcases family_descends (prefixWord ++ tailWord_274778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274784 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 3]
def baseStart_274784 : Nat := 118140960795 + 274784 * 2 ^ 59
def prefixEnd_274784 : Nat := 4983230072969 + 3 ^ 40 * 274784 * 2
def baseEnd_274784 : Nat := 125418905035696124476709

theorem tailTrace_274784 : CollatzResearch.WordTrace tailWord_274784 prefixEnd_274784 125418905035696124476709 := by
  unfold tailWord_274784
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011097918255986108035703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6681463891007981477380937 5011097918255986108035703)
  ·
    refine ⟨7516646877383979162053555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5011097918255986108035703 7516646877383979162053555)
    ·
      refine ⟨11274970316075968743080333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7516646877383979162053555 11274970316075968743080333)
      ·
        refine ⟨4228113868528488278655125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11274970316075968743080333 4228113868528488278655125)
        ·
          refine ⟨198192837587272888061959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4228113868528488278655125 198192837587272888061959)
          ·
            refine ⟨297289256380909332092939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198192837587272888061959 297289256380909332092939)
            ·
              refine ⟨445933884571363998139409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297289256380909332092939 445933884571363998139409)
              ·
                refine ⟨334450413428522998604557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445933884571363998139409 334450413428522998604557)
                ·
                  refine ⟨125418905035696124476709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334450413428522998604557 125418905035696124476709)
                  ·
                    rfl

theorem cell20_274784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_274784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274784 prefixEnd_274784 := by exact prefixLift 274784
  have htrace : WordTrace (prefixWord ++ tailWord_274784) baseStart_274784 baseEnd_274784 := by
    simpa [prefixWord, tailWord_274784, baseEnd_274784] using wordTrace_append hprefix tailTrace_274784
  have hstable : (prefixWord ++ tailWord_274784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274784).length < 2 ^ (prefixWord ++ tailWord_274784).sum := by decide
  have hdescent : baseEnd_274784 < baseStart_274784 := by decide
  rcases family_descends (prefixWord ++ tailWord_274784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274836 : List Nat := [2, 4, 2, 1, 4, 1, 6]
def baseStart_274836 : Nat := 118140960795 + 274836 * 2 ^ 59
def prefixEnd_274836 : Nat := 4983230072969 + 3 ^ 40 * 274836 * 2
def baseEnd_274836 : Nat := 13938071028068339415907

theorem tailTrace_274836 : CollatzResearch.WordTrace tailWord_274836 prefixEnd_274836 13938071028068339415907 := by
  unfold tailWord_274836
  simp only [CollatzResearch.WordTrace]
  refine ⟨5012046216161792548482181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6682728288215723397976241 5012046216161792548482181)
  ·
    refine ⟨939758665530336102840409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5012046216161792548482181 939758665530336102840409)
    ·
      refine ⟨704818999147752077130307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 939758665530336102840409 704818999147752077130307)
      ·
        refine ⟨1057228498721628115695461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 704818999147752077130307 1057228498721628115695461)
        ·
          refine ⟨198230343510305271692899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1057228498721628115695461 198230343510305271692899)
          ·
            refine ⟨297345515265457907539349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198230343510305271692899 297345515265457907539349)
            ·
              refine ⟨13938071028068339415907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 297345515265457907539349 13938071028068339415907)
              ·
                rfl

theorem cell20_274836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 6].length) (baseStart_274836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274836 prefixEnd_274836 := by exact prefixLift 274836
  have htrace : WordTrace (prefixWord ++ tailWord_274836) baseStart_274836 baseEnd_274836 := by
    simpa [prefixWord, tailWord_274836, baseEnd_274836] using wordTrace_append hprefix tailTrace_274836
  have hstable : (prefixWord ++ tailWord_274836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274836).length < 2 ^ (prefixWord ++ tailWord_274836).sum := by decide
  have hdescent : baseEnd_274836 < baseStart_274836 := by decide
  rcases family_descends (prefixWord ++ tailWord_274836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274840 : List Nat := [2, 1, 2, 5, 1, 1, 8]
def baseStart_274840 : Nat := 118140960795 + 274840 * 2 ^ 59
def prefixEnd_274840 : Nat := 4983230072969 + 3 ^ 40 * 274840 * 2
def baseEnd_274840 : Nat := 13938273884623202067757

theorem tailTrace_274840 : CollatzResearch.WordTrace tailWord_274840 prefixEnd_274840 13938273884623202067757 := by
  unfold tailWord_274840
  simp only [CollatzResearch.WordTrace]
  refine ⟨5012119162154546890054987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6682825549539395853406649 5012119162154546890054987)
  ·
    refine ⟨7518178743231820335082481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5012119162154546890054987 7518178743231820335082481)
    ·
      refine ⟨5638634057423865251311861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7518178743231820335082481 5638634057423865251311861)
      ·
        refine ⟨528621942883487367310487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5638634057423865251311861 528621942883487367310487)
        ·
          refine ⟨792932914325231050965731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528621942883487367310487 792932914325231050965731)
          ·
            refine ⟨1189399371487846576448597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792932914325231050965731 1189399371487846576448597)
            ·
              refine ⟨13938273884623202067757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1189399371487846576448597 13938273884623202067757)
              ·
                rfl

theorem cell20_274840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 8].length) (baseStart_274840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274840 prefixEnd_274840 := by exact prefixLift 274840
  have htrace : WordTrace (prefixWord ++ tailWord_274840) baseStart_274840 baseEnd_274840 := by
    simpa [prefixWord, tailWord_274840, baseEnd_274840] using wordTrace_append hprefix tailTrace_274840
  have hstable : (prefixWord ++ tailWord_274840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274840).length < 2 ^ (prefixWord ++ tailWord_274840).sum := by decide
  have hdescent : baseEnd_274840 < baseStart_274840 := by decide
  rcases family_descends (prefixWord ++ tailWord_274840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274847 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_274847 : Nat := 118140960795 + 274847 * 2 ^ 59
def prefixEnd_274847 : Nat := 4983230072969 + 3 ^ 40 * 274847 * 2
def baseEnd_274847 : Nat := 125447659952347905376451

theorem tailTrace_274847 : CollatzResearch.WordTrace tailWord_274847 prefixEnd_274847 125447659952347905376451 := by
  unfold tailWord_274847
  simp only [CollatzResearch.WordTrace]
  refine ⟨10024493635283733975614795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6682995756855822650409863 10024493635283733975614795)
  ·
    refine ⟨15036740452925600963422193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10024493635283733975614795 15036740452925600963422193)
    ·
      refine ⟨11277555339694200722566645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15036740452925600963422193 11277555339694200722566645)
      ·
        refine ⟨1057270813096331317740623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11277555339694200722566645 1057270813096331317740623)
        ·
          refine ⟨1585906219644496976610935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057270813096331317740623 1585906219644496976610935)
          ·
            refine ⟨2378859329466745464916403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585906219644496976610935 2378859329466745464916403)
            ·
              refine ⟨3568288994200118197374605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378859329466745464916403 3568288994200118197374605)
              ·
                refine ⟨1338108372825044324015477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3568288994200118197374605 1338108372825044324015477)
                ·
                  refine ⟨125447659952347905376451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1338108372825044324015477 125447659952347905376451)
                  ·
                    rfl

theorem cell20_274847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_274847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274847 prefixEnd_274847 := by exact prefixLift 274847
  have htrace : WordTrace (prefixWord ++ tailWord_274847) baseStart_274847 baseEnd_274847 := by
    simpa [prefixWord, tailWord_274847, baseEnd_274847] using wordTrace_append hprefix tailTrace_274847
  have hstable : (prefixWord ++ tailWord_274847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274847).length < 2 ^ (prefixWord ++ tailWord_274847).sum := by decide
  have hdescent : baseEnd_274847 < baseStart_274847 := by decide
  rcases family_descends (prefixWord ++ tailWord_274847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274878 : List Nat := [4, 2, 1, 1, 1, 1, 4, 6]
def baseStart_274878 : Nat := 118140960795 + 274878 * 2 ^ 59
def prefixEnd_274878 : Nat := 4983230072969 + 3 ^ 40 * 274878 * 2
def baseEnd_274878 : Nat := 41820603065683191780997

theorem tailTrace_274878 : CollatzResearch.WordTrace tailWord_274878 prefixEnd_274878 41820603065683191780997 := by
  unfold tailWord_274878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253203037271428283749161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6683749532114284179995525 1253203037271428283749161)
  ·
    refine ⟨939902277953571212811871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1253203037271428283749161 939902277953571212811871)
    ·
      refine ⟨1409853416930356819217807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 939902277953571212811871 1409853416930356819217807)
      ·
        refine ⟨2114780125395535228826711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1409853416930356819217807 2114780125395535228826711)
        ·
          refine ⟨3172170188093302843240067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2114780125395535228826711 3172170188093302843240067)
          ·
            refine ⟨4758255282139954264860101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3172170188093302843240067 4758255282139954264860101)
            ·
              refine ⟨892172865401241424661269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4758255282139954264860101 892172865401241424661269)
              ·
                refine ⟨41820603065683191780997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 892172865401241424661269 41820603065683191780997)
                ·
                  rfl

theorem cell20_274878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_274878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274878 prefixEnd_274878 := by exact prefixLift 274878
  have htrace : WordTrace (prefixWord ++ tailWord_274878) baseStart_274878 baseEnd_274878 := by
    simpa [prefixWord, tailWord_274878, baseEnd_274878] using wordTrace_append hprefix tailTrace_274878
  have hstable : (prefixWord ++ tailWord_274878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274878).length < 2 ^ (prefixWord ++ tailWord_274878).sum := by decide
  have hdescent : baseEnd_274878 < baseStart_274878 := by decide
  rcases family_descends (prefixWord ++ tailWord_274878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274898 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_274898 : Nat := 118140960795 + 274898 * 2 ^ 59
def prefixEnd_274898 : Nat := 4983230072969 + 3 ^ 40 * 274898 * 2
def baseEnd_274898 : Nat := 125470937742018394676243

theorem tailTrace_274898 : CollatzResearch.WordTrace tailWord_274898 prefixEnd_274898 125470937742018394676243 := by
  unfold tailWord_274898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2506588439524742421430337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6684235838732646457147565 2506588439524742421430337)
  ·
    refine ⟨1879941329643556816072753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2506588439524742421430337 1879941329643556816072753)
    ·
      refine ⟨1409955997232667612054565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1879941329643556816072753 1409955997232667612054565)
      ·
        refine ⟨264366749481125177260231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1409955997232667612054565 264366749481125177260231)
        ·
          refine ⟨396550124221687765890347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264366749481125177260231 396550124221687765890347)
          ·
            refine ⟨594825186332531648835521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396550124221687765890347 594825186332531648835521)
            ·
              refine ⟨446118889749398736626641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594825186332531648835521 446118889749398736626641)
              ·
                refine ⟨334589167312049052469981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446118889749398736626641 334589167312049052469981)
                ·
                  refine ⟨125470937742018394676243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334589167312049052469981 125470937742018394676243)
                  ·
                    rfl

theorem cell20_274898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_274898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274898 prefixEnd_274898 := by exact prefixLift 274898
  have htrace : WordTrace (prefixWord ++ tailWord_274898) baseStart_274898 baseEnd_274898 := by
    simpa [prefixWord, tailWord_274898, baseEnd_274898] using wordTrace_append hprefix tailTrace_274898
  have hstable : (prefixWord ++ tailWord_274898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274898).length < 2 ^ (prefixWord ++ tailWord_274898).sum := by decide
  have hdescent : baseEnd_274898 < baseStart_274898 := by decide
  rcases family_descends (prefixWord ++ tailWord_274898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274909 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_274909 : Nat := 118140960795 + 274909 * 2 ^ 59
def prefixEnd_274909 : Nat := 4983230072969 + 3 ^ 40 * 274909 * 2
def baseEnd_274909 : Nat := 125475958441751245309531

theorem tailTrace_274909 : CollatzResearch.WordTrace tailWord_274909 prefixEnd_274909 125475958441751245309531 := by
  unfold tailWord_274909
  simp only [CollatzResearch.WordTrace]
  refine ⟨10026754961059118564371781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6684503307372745709581187 10026754961059118564371781)
  ·
    refine ⟨1880016555198584730819709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10026754961059118564371781 1880016555198584730819709)
    ·
      refine ⟨705006208199469274057391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1880016555198584730819709 705006208199469274057391)
      ·
        refine ⟨1057509312299203911086087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705006208199469274057391 1057509312299203911086087)
        ·
          refine ⟨1586263968448805866629131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057509312299203911086087 1586263968448805866629131)
          ·
            refine ⟨2379395952673208799943697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586263968448805866629131 2379395952673208799943697)
            ·
              refine ⟨1784546964504906599957773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379395952673208799943697 1784546964504906599957773)
              ·
                refine ⟨669205111689339974984165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1784546964504906599957773 669205111689339974984165)
                ·
                  refine ⟨125475958441751245309531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 669205111689339974984165 125475958441751245309531)
                  ·
                    rfl

theorem cell20_274909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_274909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274909 prefixEnd_274909 := by exact prefixLift 274909
  have htrace : WordTrace (prefixWord ++ tailWord_274909) baseStart_274909 baseEnd_274909 := by
    simpa [prefixWord, tailWord_274909, baseEnd_274909] using wordTrace_append hprefix tailTrace_274909
  have hstable : (prefixWord ++ tailWord_274909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274909).length < 2 ^ (prefixWord ++ tailWord_274909).sum := by decide
  have hdescent : baseEnd_274909 < baseStart_274909 := by decide
  rcases family_descends (prefixWord ++ tailWord_274909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274923 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 3]
def baseStart_274923 : Nat := 118140960795 + 274923 * 2 ^ 59
def prefixEnd_274923 : Nat := 4983230072969 + 3 ^ 40 * 274923 * 2
def baseEnd_274923 : Nat := 125482348423229418842807

theorem tailTrace_274923 : CollatzResearch.WordTrace tailWord_274923 prefixEnd_274923 125482348423229418842807 := by
  unfold tailWord_274923
  simp only [CollatzResearch.WordTrace]
  refine ⟨10027265583008398955381423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6684843722005599303587615 10027265583008398955381423)
  ·
    refine ⟨15040898374512598433072135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10027265583008398955381423 15040898374512598433072135)
    ·
      refine ⟨22561347561768897649608203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15040898374512598433072135 22561347561768897649608203)
      ·
        refine ⟨33842021342653346474412305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22561347561768897649608203 33842021342653346474412305)
        ·
          refine ⟨25381516006990009855809229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33842021342653346474412305 25381516006990009855809229)
          ·
            refine ⟨9518068502621253695928461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25381516006990009855809229 9518068502621253695928461)
            ·
              refine ⟨3569275688482970135973173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9518068502621253695928461 3569275688482970135973173)
              ·
                refine ⟨334619595795278450247485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3569275688482970135973173 334619595795278450247485)
                ·
                  refine ⟨125482348423229418842807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334619595795278450247485 125482348423229418842807)
                  ·
                    rfl

theorem cell20_274923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 3].length) (baseStart_274923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274923 prefixEnd_274923 := by exact prefixLift 274923
  have htrace : WordTrace (prefixWord ++ tailWord_274923) baseStart_274923 baseEnd_274923 := by
    simpa [prefixWord, tailWord_274923, baseEnd_274923] using wordTrace_append hprefix tailTrace_274923
  have hstable : (prefixWord ++ tailWord_274923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274923).length < 2 ^ (prefixWord ++ tailWord_274923).sum := by decide
  have hdescent : baseEnd_274923 < baseStart_274923 := by decide
  rcases family_descends (prefixWord ++ tailWord_274923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274937 : List Nat := [1, 2, 1, 3, 1, 2, 2, 8]
def baseStart_274937 : Nat := 118140960795 + 274937 * 2 ^ 59
def prefixEnd_274937 : Nat := 4983230072969 + 3 ^ 40 * 274937 * 2
def baseEnd_274937 : Nat := 41829579468235864125361

theorem tailTrace_274937 : CollatzResearch.WordTrace tailWord_274937 prefixEnd_274937 41829579468235864125361 := by
  unfold tailWord_274937
  simp only [CollatzResearch.WordTrace]
  refine ⟨10027776204957679346391065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6685184136638452897594043 10027776204957679346391065)
  ·
    refine ⟨7520832153718259509793299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10027776204957679346391065 7520832153718259509793299)
    ·
      refine ⟨11281248230577389264689949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7520832153718259509793299 11281248230577389264689949)
      ·
        refine ⟨4230468086466520974258731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11281248230577389264689949 4230468086466520974258731)
        ·
          refine ⟨6345702129699781461388097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4230468086466520974258731 6345702129699781461388097)
          ·
            refine ⟨4759276597274836096041073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6345702129699781461388097 4759276597274836096041073)
            ·
              refine ⟨3569457447956127072030805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4759276597274836096041073 3569457447956127072030805)
              ·
                refine ⟨41829579468235864125361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3569457447956127072030805 41829579468235864125361)
                ·
                  rfl

theorem cell20_274937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_274937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274937 prefixEnd_274937 := by exact prefixLift 274937
  have htrace : WordTrace (prefixWord ++ tailWord_274937) baseStart_274937 baseEnd_274937 := by
    simpa [prefixWord, tailWord_274937, baseEnd_274937] using wordTrace_append hprefix tailTrace_274937
  have hstable : (prefixWord ++ tailWord_274937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274937).length < 2 ^ (prefixWord ++ tailWord_274937).sum := by decide
  have hdescent : baseEnd_274937 < baseStart_274937 := by decide
  rcases family_descends (prefixWord ++ tailWord_274937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274961 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 3]
def baseStart_274961 : Nat := 118140960795 + 274961 * 2 ^ 59
def prefixEnd_274961 : Nat := 4983230072969 + 3 ^ 40 * 274961 * 2
def baseEnd_274961 : Nat := 125499692658670175575985

theorem tailTrace_274961 : CollatzResearch.WordTrace tailWord_274961 prefixEnd_274961 125499692658670175575985 := by
  unfold tailWord_274961
  simp only [CollatzResearch.WordTrace]
  refine ⟨10028651556870731445264737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6685767704580487630176491 10028651556870731445264737)
  ·
    refine ⟨7521488667653048583948553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10028651556870731445264737 7521488667653048583948553)
    ·
      refine ⟨5641116500739786437961415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7521488667653048583948553 5641116500739786437961415)
      ·
        refine ⟨8461674751109679656942123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5641116500739786437961415 8461674751109679656942123)
        ·
          refine ⟨12692512126664519485413185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8461674751109679656942123 12692512126664519485413185)
          ·
            refine ⟨9519384094998389614059889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12692512126664519485413185 9519384094998389614059889)
            ·
              refine ⟨7139538071248792210544917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9519384094998389614059889 7139538071248792210544917)
              ·
                refine ⟨334665847089787134869293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7139538071248792210544917 334665847089787134869293)
                ·
                  refine ⟨125499692658670175575985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334665847089787134869293 125499692658670175575985)
                  ·
                    rfl

theorem cell20_274961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_274961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274961 prefixEnd_274961 := by exact prefixLift 274961
  have htrace : WordTrace (prefixWord ++ tailWord_274961) baseStart_274961 baseEnd_274961 := by
    simpa [prefixWord, tailWord_274961, baseEnd_274961] using wordTrace_append hprefix tailTrace_274961
  have hstable : (prefixWord ++ tailWord_274961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274961).length < 2 ^ (prefixWord ++ tailWord_274961).sum := by decide
  have hdescent : baseEnd_274961 < baseStart_274961 := by decide
  rcases family_descends (prefixWord ++ tailWord_274961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274964 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 4]
def baseStart_274964 : Nat := 118140960795 + 274964 * 2 ^ 59
def prefixEnd_274964 : Nat := 4983230072969 + 3 ^ 40 * 274964 * 2
def baseEnd_274964 : Nat := 125501061940415498475973

theorem tailTrace_274964 : CollatzResearch.WordTrace tailWord_274964 prefixEnd_274964 125501061940415498475973 := by
  unfold tailWord_274964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014380487929931478811973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6685840650573241971749297 5014380487929931478811973)
  ·
    refine ⟨940196341486862152277245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5014380487929931478811973 940196341486862152277245)
    ·
      refine ⟨352573628057573307103967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 940196341486862152277245 352573628057573307103967)
      ·
        refine ⟨528860442086359960655951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352573628057573307103967 528860442086359960655951)
        ·
          refine ⟨793290663129539940983927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528860442086359960655951 793290663129539940983927)
          ·
            refine ⟨1189935994694309911475891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793290663129539940983927 1189935994694309911475891)
            ·
              refine ⟨1784903992041464867213837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189935994694309911475891 1784903992041464867213837)
              ·
                refine ⟨669338997015549325205189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1784903992041464867213837 669338997015549325205189)
                ·
                  refine ⟨125501061940415498475973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 669338997015549325205189 125501061940415498475973)
                  ·
                    rfl

theorem cell20_274964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_274964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274964 prefixEnd_274964 := by exact prefixLift 274964
  have htrace : WordTrace (prefixWord ++ tailWord_274964) baseStart_274964 baseEnd_274964 := by
    simpa [prefixWord, tailWord_274964, baseEnd_274964] using wordTrace_append hprefix tailTrace_274964
  have hstable : (prefixWord ++ tailWord_274964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274964).length < 2 ^ (prefixWord ++ tailWord_274964).sum := by decide
  have hdescent : baseEnd_274964 < baseStart_274964 := by decide
  rcases family_descends (prefixWord ++ tailWord_274964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274975 : List Nat := [1, 1, 2, 4, 1, 1, 1, 9]
def baseStart_274975 : Nat := 118140960795 + 274975 * 2 ^ 59
def prefixEnd_274975 : Nat := 4983230072969 + 3 ^ 40 * 274975 * 2
def baseEnd_274975 : Nat := 41835360880049449703087

theorem tailTrace_274975 : CollatzResearch.WordTrace tailWord_274975 prefixEnd_274975 41835360880049449703087 := by
  unfold tailWord_274975
  simp only [CollatzResearch.WordTrace]
  refine ⟨10029162178820011836274379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6686108119213341224182919 10029162178820011836274379)
  ·
    refine ⟨15043743268230017754411569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10029162178820011836274379 15043743268230017754411569)
    ·
      refine ⟨11282807451172513315808677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15043743268230017754411569 11282807451172513315808677)
      ·
        refine ⟨2115526397094846246714127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11282807451172513315808677 2115526397094846246714127)
        ·
          refine ⟨3173289595642269370071191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2115526397094846246714127 3173289595642269370071191)
          ·
            refine ⟨4759934393463404055106787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173289595642269370071191 4759934393463404055106787)
            ·
              refine ⟨7139901590195106082660181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759934393463404055106787 7139901590195106082660181)
              ·
                refine ⟨41835360880049449703087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7139901590195106082660181 41835360880049449703087)
                ·
                  rfl

theorem cell20_274975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_274975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274975 prefixEnd_274975 := by exact prefixLift 274975
  have htrace : WordTrace (prefixWord ++ tailWord_274975) baseStart_274975 baseEnd_274975 := by
    simpa [prefixWord, tailWord_274975, baseEnd_274975] using wordTrace_append hprefix tailTrace_274975
  have hstable : (prefixWord ++ tailWord_274975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274975).length < 2 ^ (prefixWord ++ tailWord_274975).sum := by decide
  have hdescent : baseEnd_274975 < baseStart_274975 := by decide
  rcases family_descends (prefixWord ++ tailWord_274975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274992 : List Nat := [2, 1, 1, 1, 2, 3, 6, 4]
def baseStart_274992 : Nat := 118140960795 + 274992 * 2 ^ 59
def prefixEnd_274992 : Nat := 4983230072969 + 3 ^ 40 * 274992 * 2
def baseEnd_274992 : Nat := 41837947301123948514175

theorem tailTrace_274992 : CollatzResearch.WordTrace tailWord_274992 prefixEnd_274992 41837947301123948514175 := by
  unfold tailWord_274992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014891109879211869821615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6686521479838949159762153 5014891109879211869821615)
  ·
    refine ⟨7522336664818817804732423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5014891109879211869821615 7522336664818817804732423)
    ·
      refine ⟨11283504997228226707098635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7522336664818817804732423 11283504997228226707098635)
      ·
        refine ⟨16925257495842340060647953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11283504997228226707098635 16925257495842340060647953)
        ·
          refine ⟨12693943121881755045485965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16925257495842340060647953 12693943121881755045485965)
          ·
            refine ⟨4760228670705658142057237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12693943121881755045485965 4760228670705658142057237)
            ·
              refine ⟨223135718939327725408933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4760228670705658142057237 223135718939327725408933)
              ·
                refine ⟨41837947301123948514175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223135718939327725408933 41837947301123948514175)
                ·
                  rfl

theorem cell20_274992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_274992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274992 prefixEnd_274992 := by exact prefixLift 274992
  have htrace : WordTrace (prefixWord ++ tailWord_274992) baseStart_274992 baseEnd_274992 := by
    simpa [prefixWord, tailWord_274992, baseEnd_274992] using wordTrace_append hprefix tailTrace_274992
  have hstable : (prefixWord ++ tailWord_274992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274992).length < 2 ^ (prefixWord ++ tailWord_274992).sum := by decide
  have hdescent : baseEnd_274992 < baseStart_274992 := by decide
  rcases family_descends (prefixWord ++ tailWord_274992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274998 : List Nat := [5, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_274998 : Nat := 118140960795 + 274998 * 2 ^ 59
def prefixEnd_274998 : Nat := 4983230072969 + 3 ^ 40 * 274998 * 2
def baseEnd_274998 : Nat := 125516580466862491342501

theorem tailTrace_274998 : CollatzResearch.WordTrace tailWord_274998 prefixEnd_274998 125516580466862491342501 := by
  unfold tailWord_274998
  simp only [CollatzResearch.WordTrace]
  refine ⟨626875066108542922772603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6686667371824457842907765 626875066108542922772603)
  ·
    refine ⟨940312599162814384158905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 626875066108542922772603 940312599162814384158905)
    ·
      refine ⟨705234449372110788119179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 940312599162814384158905 705234449372110788119179)
      ·
        refine ⟨1057851674058166182178769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705234449372110788119179 1057851674058166182178769)
        ·
          refine ⟨793388755543624636634077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1057851674058166182178769 793388755543624636634077)
          ·
            refine ⟨297520783328859238737779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 793388755543624636634077 297520783328859238737779)
            ·
              refine ⟨446281174993288858106669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297520783328859238737779 446281174993288858106669)
              ·
                refine ⟨167355440622483321790001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446281174993288858106669 167355440622483321790001)
                ·
                  refine ⟨125516580466862491342501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167355440622483321790001 125516580466862491342501)
                  ·
                    rfl

theorem cell20_274998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_274998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_274998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_274998 prefixEnd_274998 := by exact prefixLift 274998
  have htrace : WordTrace (prefixWord ++ tailWord_274998) baseStart_274998 baseEnd_274998 := by
    simpa [prefixWord, tailWord_274998, baseEnd_274998] using wordTrace_append hprefix tailTrace_274998
  have hstable : (prefixWord ++ tailWord_274998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274998).length < 2 ^ (prefixWord ++ tailWord_274998).sum := by decide
  have hdescent : baseEnd_274998 < baseStart_274998 := by decide
  rcases family_descends (prefixWord ++ tailWord_274998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275002 : List Nat := [3, 1, 1, 1, 3, 3, 3, 3, 2]
def baseStart_275002 : Nat := 118140960795 + 275002 * 2 ^ 59
def prefixEnd_275002 : Nat := 4983230072969 + 3 ^ 40 * 275002 * 2
def baseEnd_275002 : Nat := 125518406175856255209151

theorem tailTrace_275002 : CollatzResearch.WordTrace tailWord_275002 prefixEnd_275002 125518406175856255209151 := by
  unfold tailWord_275002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2507536737430548861876815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6686764633148130298338173 2507536737430548861876815)
  ·
    refine ⟨3761305106145823292815223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2507536737430548861876815 3761305106145823292815223)
    ·
      refine ⟨5641957659218734939222835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3761305106145823292815223 5641957659218734939222835)
      ·
        refine ⟨8462936488828102408834253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5641957659218734939222835 8462936488828102408834253)
        ·
          refine ⟨3173601183310538403312845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8462936488828102408834253 3173601183310538403312845)
          ·
            refine ⟨1190100443741451901242317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3173601183310538403312845 1190100443741451901242317)
            ·
              refine ⟨446287666403044462965869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1190100443741451901242317 446287666403044462965869)
              ·
                refine ⟨167357874901141673612201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446287666403044462965869 167357874901141673612201)
                ·
                  refine ⟨125518406175856255209151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167357874901141673612201 125518406175856255209151)
                  ·
                    rfl

theorem cell20_275002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_275002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275002 prefixEnd_275002 := by exact prefixLift 275002
  have htrace : WordTrace (prefixWord ++ tailWord_275002) baseStart_275002 baseEnd_275002 := by
    simpa [prefixWord, tailWord_275002, baseEnd_275002] using wordTrace_append hprefix tailTrace_275002
  have hstable : (prefixWord ++ tailWord_275002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275002).length < 2 ^ (prefixWord ++ tailWord_275002).sum := by decide
  have hdescent : baseEnd_275002 < baseStart_275002 := by decide
  rcases family_descends (prefixWord ++ tailWord_275002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275013 : List Nat := [1, 3, 1, 1, 1, 5, 8]
def baseStart_275013 : Nat := 118140960795 + 275013 * 2 ^ 59
def prefixEnd_275013 : Nat := 4983230072969 + 3 ^ 40 * 275013 * 2
def baseEnd_275013 : Nat := 13947047430621011760271

theorem tailTrace_275013 : CollatzResearch.WordTrace tailWord_275013 prefixEnd_275013 13947047430621011760271 := by
  unfold tailWord_275013
  simp only [CollatzResearch.WordTrace]
  refine ⟨10030548152682344326157693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6687032101788229550771795 10030548152682344326157693)
  ·
    refine ⟨3761455557255879122309135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10030548152682344326157693 3761455557255879122309135)
    ·
      refine ⟨5642183335883818683463703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3761455557255879122309135 5642183335883818683463703)
      ·
        refine ⟨8463275003825728025195555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5642183335883818683463703 8463275003825728025195555)
        ·
          refine ⟨12694912505738592037793333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8463275003825728025195555 12694912505738592037793333)
          ·
            refine ⟨1190148047412993003543125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12694912505738592037793333 1190148047412993003543125)
            ·
              refine ⟨13947047430621011760271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1190148047412993003543125 13947047430621011760271)
              ·
                rfl

theorem cell20_275013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 8].length) (baseStart_275013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275013 prefixEnd_275013 := by exact prefixLift 275013
  have htrace : WordTrace (prefixWord ++ tailWord_275013) baseStart_275013 baseEnd_275013 := by
    simpa [prefixWord, tailWord_275013, baseEnd_275013] using wordTrace_append hprefix tailTrace_275013
  have hstable : (prefixWord ++ tailWord_275013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275013).length < 2 ^ (prefixWord ++ tailWord_275013).sum := by decide
  have hdescent : baseEnd_275013 < baseStart_275013 := by decide
  rcases family_descends (prefixWord ++ tailWord_275013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275023 : List Nat := [1, 1, 2, 1, 1, 2, 4, 6, 2]
def baseStart_275023 : Nat := 118140960795 + 275023 * 2 ^ 59
def prefixEnd_275023 : Nat := 4983230072969 + 3 ^ 40 * 275023 * 2
def baseEnd_275023 : Nat := 125527991148073515509065

theorem tailTrace_275023 : CollatzResearch.WordTrace tailWord_275023 prefixEnd_275023 125527991148073515509065 := by
  unfold tailWord_275023
  simp only [CollatzResearch.WordTrace]
  refine ⟨10030912882646116034021723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6687275255097410689347815 10030912882646116034021723)
  ·
    refine ⟨15046369323969174051032585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10030912882646116034021723 15046369323969174051032585)
    ·
      refine ⟨11284776992976880538274439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15046369323969174051032585 11284776992976880538274439)
      ·
        refine ⟨16927165489465320807411659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11284776992976880538274439 16927165489465320807411659)
        ·
          refine ⟨25390748234197981211117489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16927165489465320807411659 25390748234197981211117489)
          ·
            refine ⟨19043061175648485908338117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25390748234197981211117489 19043061175648485908338117)
            ·
              refine ⟨3570573970434091107813397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19043061175648485908338117 3570573970434091107813397)
              ·
                refine ⟨167370654864098020678753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3570573970434091107813397 167370654864098020678753)
                ·
                  refine ⟨125527991148073515509065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167370654864098020678753 125527991148073515509065)
                  ·
                    rfl

theorem cell20_275023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 2].length) (baseStart_275023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275023 prefixEnd_275023 := by exact prefixLift 275023
  have htrace : WordTrace (prefixWord ++ tailWord_275023) baseStart_275023 baseEnd_275023 := by
    simpa [prefixWord, tailWord_275023, baseEnd_275023] using wordTrace_append hprefix tailTrace_275023
  have hstable : (prefixWord ++ tailWord_275023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275023).length < 2 ^ (prefixWord ++ tailWord_275023).sum := by decide
  have hdescent : baseEnd_275023 < baseStart_275023 := by decide
  rcases family_descends (prefixWord ++ tailWord_275023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275044 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_275044 : Nat := 118140960795 + 275044 * 2 ^ 59
def prefixEnd_275044 : Nat := 4983230072969 + 3 ^ 40 * 275044 * 2
def baseEnd_275044 : Nat := 125537576120290775808979

theorem tailTrace_275044 : CollatzResearch.WordTrace tailWord_275044 prefixEnd_275044 125537576120290775808979 := by
  unfold tailWord_275044
  simp only [CollatzResearch.WordTrace]
  refine ⟨5015839407785018310268093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6687785877046691080357457 5015839407785018310268093)
  ·
    refine ⟨1880939777919381866350535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5015839407785018310268093 1880939777919381866350535)
    ·
      refine ⟨2821409666879072799525803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1880939777919381866350535 2821409666879072799525803)
      ·
        refine ⟨4232114500318609199288705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821409666879072799525803 4232114500318609199288705)
        ·
          refine ⟨3174085875238956899466529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4232114500318609199288705 3174085875238956899466529)
          ·
            refine ⟨2380564406429217674599897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3174085875238956899466529 2380564406429217674599897)
            ·
              refine ⟨1785423304821913255949923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2380564406429217674599897 1785423304821913255949923)
              ·
                refine ⟨2678134957232869883924885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785423304821913255949923 2678134957232869883924885)
                ·
                  refine ⟨125537576120290775808979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2678134957232869883924885 125537576120290775808979)
                  ·
                    rfl

theorem cell20_275044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_275044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275044 prefixEnd_275044 := by exact prefixLift 275044
  have htrace : WordTrace (prefixWord ++ tailWord_275044) baseStart_275044 baseEnd_275044 := by
    simpa [prefixWord, tailWord_275044, baseEnd_275044] using wordTrace_append hprefix tailTrace_275044
  have hstable : (prefixWord ++ tailWord_275044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275044).length < 2 ^ (prefixWord ++ tailWord_275044).sum := by decide
  have hdescent : baseEnd_275044 < baseStart_275044 := by decide
  rcases family_descends (prefixWord ++ tailWord_275044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275075 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 3]
def baseStart_275075 : Nat := 118140960795 + 275075 * 2 ^ 59
def prefixEnd_275075 : Nat := 4983230072969 + 3 ^ 40 * 275075 * 2
def baseEnd_275075 : Nat := 125551725364992445775519

theorem tailTrace_275075 : CollatzResearch.WordTrace tailWord_275075 prefixEnd_275075 125551725364992445775519 := by
  unfold tailWord_275075
  simp only [CollatzResearch.WordTrace]
  refine ⟨10032809478457728914914679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6688539652305152609943119 10032809478457728914914679)
  ·
    refine ⟨15049214217686593372372019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10032809478457728914914679 15049214217686593372372019)
    ·
      refine ⟨22573821326529890058558029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15049214217686593372372019 22573821326529890058558029)
      ·
        refine ⟨8465182997448708771959261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22573821326529890058558029 8465182997448708771959261)
        ·
          refine ⟨3174443624043265789484723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8465182997448708771959261 3174443624043265789484723)
          ·
            refine ⟨4761665436064898684227085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174443624043265789484723 4761665436064898684227085)
            ·
              refine ⟨1785624538524337006585157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4761665436064898684227085 1785624538524337006585157)
              ·
                refine ⟨334804600973313188734717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1785624538524337006585157 334804600973313188734717)
                ·
                  refine ⟨125551725364992445775519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334804600973313188734717 125551725364992445775519)
                  ·
                    rfl

theorem cell20_275075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 3].length) (baseStart_275075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275075 prefixEnd_275075 := by exact prefixLift 275075
  have htrace : WordTrace (prefixWord ++ tailWord_275075) baseStart_275075 baseEnd_275075 := by
    simpa [prefixWord, tailWord_275075, baseEnd_275075] using wordTrace_append hprefix tailTrace_275075
  have hstable : (prefixWord ++ tailWord_275075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275075).length < 2 ^ (prefixWord ++ tailWord_275075).sum := by decide
  have hdescent : baseEnd_275075 < baseStart_275075 := by decide
  rcases family_descends (prefixWord ++ tailWord_275075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275157 : List Nat := [1, 3, 2, 5, 2, 1, 2, 4]
def baseStart_275157 : Nat := 118140960795 + 275157 * 2 ^ 59
def prefixEnd_275157 : Nat := 4983230072969 + 3 ^ 40 * 275157 * 2
def baseEnd_275157 : Nat := 41863050799788201680617

theorem tailTrace_275157 : CollatzResearch.WordTrace tailWord_275157 prefixEnd_275157 41863050799788201680617 := by
  unfold tailWord_275157
  simp only [CollatzResearch.WordTrace]
  refine ⟨10035800264160656919399725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6690533509440437946266483 10035800264160656919399725)
  ·
    refine ⟨3763425099060246344774897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10035800264160656919399725 3763425099060246344774897)
    ·
      refine ⟨2822568824295184758581173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3763425099060246344774897 2822568824295184758581173)
      ·
        refine ⟨264615827277673571116985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2822568824295184758581173 264615827277673571116985)
        ·
          refine ⟨198461870458255178337739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264615827277673571116985 198461870458255178337739)
          ·
            refine ⟨297692805687382767506609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198461870458255178337739 297692805687382767506609)
            ·
              refine ⟨223269604265537075629957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297692805687382767506609 223269604265537075629957)
              ·
                refine ⟨41863050799788201680617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223269604265537075629957 41863050799788201680617)
                ·
                  rfl

theorem cell20_275157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 4].length) (baseStart_275157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275157 prefixEnd_275157 := by exact prefixLift 275157
  have htrace : WordTrace (prefixWord ++ tailWord_275157) baseStart_275157 baseEnd_275157 := by
    simpa [prefixWord, tailWord_275157, baseEnd_275157] using wordTrace_append hprefix tailTrace_275157
  have hstable : (prefixWord ++ tailWord_275157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275157).length < 2 ^ (prefixWord ++ tailWord_275157).sum := by decide
  have hdescent : baseEnd_275157 < baseStart_275157 := by decide
  rcases family_descends (prefixWord ++ tailWord_275157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275171 : List Nat := [1, 1, 1, 7, 1, 3, 1, 3, 2]
def baseStart_275171 : Nat := 118140960795 + 275171 * 2 ^ 59
def prefixEnd_275171 : Nat := 4983230072969 + 3 ^ 40 * 275171 * 2
def baseEnd_275171 : Nat := 125595542380842778575127

theorem tailTrace_275171 : CollatzResearch.WordTrace tailWord_275171 prefixEnd_275171 125595542380842778575127 := by
  unfold tailWord_275171
  simp only [CollatzResearch.WordTrace]
  refine ⟨10036310886109937310409367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6690873924073291540272911 10036310886109937310409367)
  ·
    refine ⟨15054466329164905965614051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10036310886109937310409367 15054466329164905965614051)
    ·
      refine ⟨22581699493747358948421077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15054466329164905965614051 22581699493747358948421077)
      ·
        refine ⟨529258581884703725353619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 22581699493747358948421077 529258581884703725353619)
        ·
          refine ⟨793887872827055588030429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529258581884703725353619 793887872827055588030429)
          ·
            refine ⟨297707952310145845511411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 793887872827055588030429 297707952310145845511411)
            ·
              refine ⟨446561928465218768267117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297707952310145845511411 446561928465218768267117)
              ·
                refine ⟨167460723174457038100169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446561928465218768267117 167460723174457038100169)
                ·
                  refine ⟨125595542380842778575127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167460723174457038100169 125595542380842778575127)
                  ·
                    rfl

theorem cell20_275171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 2].length) (baseStart_275171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275171 prefixEnd_275171 := by exact prefixLift 275171
  have htrace : WordTrace (prefixWord ++ tailWord_275171) baseStart_275171 baseEnd_275171 := by
    simpa [prefixWord, tailWord_275171, baseEnd_275171] using wordTrace_append hprefix tailTrace_275171
  have hstable : (prefixWord ++ tailWord_275171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275171).length < 2 ^ (prefixWord ++ tailWord_275171).sum := by decide
  have hdescent : baseEnd_275171 < baseStart_275171 := by decide
  rcases family_descends (prefixWord ++ tailWord_275171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275182 : List Nat := [4, 1, 2, 1, 1, 5, 6]
def baseStart_275182 : Nat := 118140960795 + 275182 * 2 ^ 59
def prefixEnd_275182 : Nat := 4983230072969 + 3 ^ 40 * 275182 * 2
def baseEnd_275182 : Nat := 13955618120063958800935

theorem tailTrace_275182 : CollatzResearch.WordTrace tailWord_275182 prefixEnd_275182 13955618120063958800935 := by
  unfold tailWord_275182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1254589011133760773632475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6691141392713390792706533 1254589011133760773632475)
  ·
    refine ⟨1881883516700641160448713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1254589011133760773632475 1881883516700641160448713)
    ·
      refine ⟨1411412637525480870336535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1881883516700641160448713 1411412637525480870336535)
      ·
        refine ⟨2117118956288221305504803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411412637525480870336535 2117118956288221305504803)
        ·
          refine ⟨3175678434432331958257205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117118956288221305504803 3175678434432331958257205)
          ·
            refine ⟨297719853228031121086613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3175678434432331958257205 297719853228031121086613)
            ·
              refine ⟨13955618120063958800935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 297719853228031121086613 13955618120063958800935)
              ·
                rfl

theorem cell20_275182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 6].length) (baseStart_275182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275182 prefixEnd_275182 := by exact prefixLift 275182
  have htrace : WordTrace (prefixWord ++ tailWord_275182) baseStart_275182 baseEnd_275182 := by
    simpa [prefixWord, tailWord_275182, baseEnd_275182] using wordTrace_append hprefix tailTrace_275182
  have hstable : (prefixWord ++ tailWord_275182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275182).length < 2 ^ (prefixWord ++ tailWord_275182).sum := by decide
  have hdescent : baseEnd_275182 < baseStart_275182 := by decide
  rcases family_descends (prefixWord ++ tailWord_275182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275188 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 4]
def baseStart_275188 : Nat := 118140960795 + 275188 * 2 ^ 59
def prefixEnd_275188 : Nat := 4983230072969 + 3 ^ 40 * 275188 * 2
def baseEnd_275188 : Nat := 125603301644066275008391

theorem tailTrace_275188 : CollatzResearch.WordTrace tailWord_275188 prefixEnd_275188 125603301644066275008391 := by
  unfold tailWord_275188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5018465463524174606889109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6691287284698899475852145 5018465463524174606889109)
  ·
    refine ⟨235240568602695684697927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5018465463524174606889109 235240568602695684697927)
    ·
      refine ⟨352860852904043527046891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235240568602695684697927 352860852904043527046891)
      ·
        refine ⟨529291279356065290570337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352860852904043527046891 529291279356065290570337)
        ·
          refine ⟨396968459517048967927753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529291279356065290570337 396968459517048967927753)
          ·
            refine ⟨297726344637786725945815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396968459517048967927753 297726344637786725945815)
            ·
              refine ⟨446589516956680088918723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297726344637786725945815 446589516956680088918723)
              ·
                refine ⟨669884275435020133378085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446589516956680088918723 669884275435020133378085)
                ·
                  refine ⟨125603301644066275008391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 669884275435020133378085 125603301644066275008391)
                  ·
                    rfl

theorem cell20_275188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_275188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275188 prefixEnd_275188 := by exact prefixLift 275188
  have htrace : WordTrace (prefixWord ++ tailWord_275188) baseStart_275188 baseEnd_275188 := by
    simpa [prefixWord, tailWord_275188, baseEnd_275188] using wordTrace_append hprefix tailTrace_275188
  have hstable : (prefixWord ++ tailWord_275188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275188).length < 2 ^ (prefixWord ++ tailWord_275188).sum := by decide
  have hdescent : baseEnd_275188 < baseStart_275188 := by decide
  rcases family_descends (prefixWord ++ tailWord_275188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275192 : List Nat := [2, 1, 2, 1, 1, 2, 7, 2, 2]
def baseStart_275192 : Nat := 118140960795 + 275192 * 2 ^ 59
def prefixEnd_275192 : Nat := 4983230072969 + 3 ^ 40 * 275192 * 2
def baseEnd_275192 : Nat := 125605127353060038875041

theorem tailTrace_275192 : CollatzResearch.WordTrace tailWord_275192 prefixEnd_275192 125605127353060038875041 := by
  unfold tailWord_275192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5018538409516928948461915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6691384546022571931282553 5018538409516928948461915)
  ·
    refine ⟨7527807614275393422692873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5018538409516928948461915 7527807614275393422692873)
    ·
      refine ⟨5645855710706545067019655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7527807614275393422692873 5645855710706545067019655)
      ·
        refine ⟨8468783566059817600529483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5645855710706545067019655 8468783566059817600529483)
        ·
          refine ⟨12703175349089726400794225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8468783566059817600529483 12703175349089726400794225)
          ·
            refine ⟨9527381511817294800595669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12703175349089726400794225 9527381511817294800595669)
            ·
              refine ⟨223298004183217846888961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9527381511817294800595669 223298004183217846888961)
              ·
                refine ⟨167473503137413385166721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223298004183217846888961 167473503137413385166721)
                ·
                  refine ⟨125605127353060038875041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167473503137413385166721 125605127353060038875041)
                  ·
                    rfl

theorem cell20_275192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_275192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275192 prefixEnd_275192 := by exact prefixLift 275192
  have htrace : WordTrace (prefixWord ++ tailWord_275192) baseStart_275192 baseEnd_275192 := by
    simpa [prefixWord, tailWord_275192, baseEnd_275192] using wordTrace_append hprefix tailTrace_275192
  have hstable : (prefixWord ++ tailWord_275192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275192).length < 2 ^ (prefixWord ++ tailWord_275192).sum := by decide
  have hdescent : baseEnd_275192 < baseStart_275192 := by decide
  rcases family_descends (prefixWord ++ tailWord_275192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275202 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_275202 : Nat := 118140960795 + 275202 * 2 ^ 59
def prefixEnd_275202 : Nat := 4983230072969 + 3 ^ 40 * 275202 * 2
def baseEnd_275202 : Nat := 125609691625544448541667

theorem tailTrace_275202 : CollatzResearch.WordTrace tailWord_275202 prefixEnd_275202 125609691625544448541667 := by
  unfold tailWord_275202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509360387249407401196965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6691627699331753069858573 2509360387249407401196965)
  ·
    refine ⟨470505072609263887724431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2509360387249407401196965 470505072609263887724431)
    ·
      refine ⟨705757608913895831586647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470505072609263887724431 705757608913895831586647)
      ·
        refine ⟨1058636413370843747379971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705757608913895831586647 1058636413370843747379971)
        ·
          refine ⟨1587954620056265621069957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058636413370843747379971 1587954620056265621069957)
          ·
            refine ⟨297741491260549803950617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1587954620056265621069957 297741491260549803950617)
            ·
              refine ⟨223306118445412352962963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297741491260549803950617 223306118445412352962963)
              ·
                refine ⟨334959177668118529444445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223306118445412352962963 334959177668118529444445)
                ·
                  refine ⟨125609691625544448541667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334959177668118529444445 125609691625544448541667)
                  ·
                    rfl

theorem cell20_275202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_275202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275202 prefixEnd_275202 := by exact prefixLift 275202
  have htrace : WordTrace (prefixWord ++ tailWord_275202) baseStart_275202 baseEnd_275202 := by
    simpa [prefixWord, tailWord_275202, baseEnd_275202] using wordTrace_append hprefix tailTrace_275202
  have hstable : (prefixWord ++ tailWord_275202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275202).length < 2 ^ (prefixWord ++ tailWord_275202).sum := by decide
  have hdescent : baseEnd_275202 < baseStart_275202 := by decide
  rcases family_descends (prefixWord ++ tailWord_275202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275248 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_275248 : Nat := 118140960795 + 275248 * 2 ^ 59
def prefixEnd_275248 : Nat := 4983230072969 + 3 ^ 40 * 275248 * 2
def baseEnd_275248 : Nat := 125630687278972733008145

theorem tailTrace_275248 : CollatzResearch.WordTrace tailWord_275248 prefixEnd_275248 125630687278972733008145 := by
  unfold tailWord_275248
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019559653415489730481199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6692746204553986307308265 5019559653415489730481199)
  ·
    refine ⟨7529339480123234595721799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5019559653415489730481199 7529339480123234595721799)
    ·
      refine ⟨11294009220184851893582699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7529339480123234595721799 11294009220184851893582699)
      ·
        refine ⟨16941013830277277840374049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11294009220184851893582699 16941013830277277840374049)
        ·
          refine ⟨12705760372707958380280537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16941013830277277840374049 12705760372707958380280537)
          ·
            refine ⟨9529320279530968785210403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12705760372707958380280537 9529320279530968785210403)
            ·
              refine ⟨14293980419296453177815605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9529320279530968785210403 14293980419296453177815605)
              ·
                refine ⟨1340060664309042485420213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14293980419296453177815605 1340060664309042485420213)
                ·
                  refine ⟨125630687278972733008145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1340060664309042485420213 125630687278972733008145)
                  ·
                    rfl

theorem cell20_275248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_275248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275248 prefixEnd_275248 := by exact prefixLift 275248
  have htrace : WordTrace (prefixWord ++ tailWord_275248) baseStart_275248 baseEnd_275248 := by
    simpa [prefixWord, tailWord_275248, baseEnd_275248] using wordTrace_append hprefix tailTrace_275248
  have hstable : (prefixWord ++ tailWord_275248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275248).length < 2 ^ (prefixWord ++ tailWord_275248).sum := by decide
  have hdescent : baseEnd_275248 < baseStart_275248 := by decide
  rcases family_descends (prefixWord ++ tailWord_275248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275254 : List Nat := [5, 1, 2, 2, 2, 2, 1, 5]
def baseStart_275254 : Nat := 118140960795 + 275254 * 2 ^ 59
def prefixEnd_275254 : Nat := 4983230072969 + 3 ^ 40 * 275254 * 2
def baseEnd_275254 : Nat := 41877808614154459602707

theorem tailTrace_275254 : CollatzResearch.WordTrace tailWord_275254 prefixEnd_275254 41877808614154459602707 := by
  unfold tailWord_275254
  simp only [CollatzResearch.WordTrace]
  refine ⟨627458634050577655355051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6692892096539494990453877 627458634050577655355051)
  ·
    refine ⟨941187951075866483032577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627458634050577655355051 941187951075866483032577)
    ·
      refine ⟨705890963306899862274433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 941187951075866483032577 705890963306899862274433)
      ·
        refine ⟨529418222480174896705825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 705890963306899862274433 529418222480174896705825)
        ·
          refine ⟨397063666860131172529369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529418222480174896705825 397063666860131172529369)
          ·
            refine ⟨297797750145098379397027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397063666860131172529369 297797750145098379397027)
            ·
              refine ⟨446696625217647569095541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297797750145098379397027 446696625217647569095541)
              ·
                refine ⟨41877808614154459602707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 446696625217647569095541 41877808614154459602707)
                ·
                  rfl

theorem cell20_275254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_275254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275254 prefixEnd_275254 := by exact prefixLift 275254
  have htrace : WordTrace (prefixWord ++ tailWord_275254) baseStart_275254 baseEnd_275254 := by
    simpa [prefixWord, tailWord_275254, baseEnd_275254] using wordTrace_append hprefix tailTrace_275254
  have hstable : (prefixWord ++ tailWord_275254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275254).length < 2 ^ (prefixWord ++ tailWord_275254).sum := by decide
  have hdescent : baseEnd_275254 < baseStart_275254 := by decide
  rcases family_descends (prefixWord ++ tailWord_275254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275272 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_275272 : Nat := 118140960795 + 275272 * 2 ^ 59
def prefixEnd_275272 : Nat := 4983230072969 + 3 ^ 40 * 275272 * 2
def baseEnd_275272 : Nat := 125641641532935316208047

theorem tailTrace_275272 : CollatzResearch.WordTrace tailWord_275272 prefixEnd_275272 125641641532935316208047 := by
  unfold tailWord_275272
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019997329372015779918035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6693329772496021039890713 5019997329372015779918035)
  ·
    refine ⟨7529995994058023669877053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5019997329372015779918035 7529995994058023669877053)
    ·
      refine ⟨2823748497771758876203895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7529995994058023669877053 2823748497771758876203895)
      ·
        refine ⟨4235622746657638314305843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2823748497771758876203895 4235622746657638314305843)
        ·
          refine ⟨6353434119986457471458765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235622746657638314305843 6353434119986457471458765)
          ·
            refine ⟨2382537794994921551797037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6353434119986457471458765 2382537794994921551797037)
            ·
              refine ⟨893451673123095581923889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2382537794994921551797037 893451673123095581923889)
              ·
                refine ⟨670088754842321686442917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893451673123095581923889 670088754842321686442917)
                ·
                  refine ⟨125641641532935316208047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670088754842321686442917 125641641532935316208047)
                  ·
                    rfl

theorem cell20_275272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_275272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275272 prefixEnd_275272 := by exact prefixLift 275272
  have htrace : WordTrace (prefixWord ++ tailWord_275272) baseStart_275272 baseEnd_275272 := by
    simpa [prefixWord, tailWord_275272, baseEnd_275272] using wordTrace_append hprefix tailTrace_275272
  have hstable : (prefixWord ++ tailWord_275272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275272).length < 2 ^ (prefixWord ++ tailWord_275272).sum := by decide
  have hdescent : baseEnd_275272 < baseStart_275272 := by decide
  rcases family_descends (prefixWord ++ tailWord_275272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275289 : List Nat := [1, 2, 1, 2, 2, 4, 1, 5, 2]
def baseStart_275289 : Nat := 118140960795 + 275289 * 2 ^ 59
def prefixEnd_275289 : Nat := 4983230072969 + 3 ^ 40 * 275289 * 2
def baseEnd_275289 : Nat := 125649400796158812641311

theorem tailTrace_275289 : CollatzResearch.WordTrace tailWord_275289 prefixEnd_275289 125649400796158812641311 := by
  unfold tailWord_275289
  simp only [CollatzResearch.WordTrace]
  refine ⟨10040614699682443463204921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6693743133121628975469947 10040614699682443463204921)
  ·
    refine ⟨7530461024761832597403691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10040614699682443463204921 7530461024761832597403691)
    ·
      refine ⟨11295691537142748896105537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7530461024761832597403691 11295691537142748896105537)
      ·
        refine ⟨8471768652857061672079153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11295691537142748896105537 8471768652857061672079153)
        ·
          refine ⟨6353826489642796254059365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8471768652857061672079153 6353826489642796254059365)
          ·
            refine ⟨1191342466808024297636131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6353826489642796254059365 1191342466808024297636131)
            ·
              refine ⟨1787013700212036446454197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191342466808024297636131 1787013700212036446454197)
              ·
                refine ⟨167532534394878416855081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1787013700212036446454197 167532534394878416855081)
                ·
                  refine ⟨125649400796158812641311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167532534394878416855081 125649400796158812641311)
                  ·
                    rfl

theorem cell20_275289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_275289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275289 prefixEnd_275289 := by exact prefixLift 275289
  have htrace : WordTrace (prefixWord ++ tailWord_275289) baseStart_275289 baseEnd_275289 := by
    simpa [prefixWord, tailWord_275289, baseEnd_275289] using wordTrace_append hprefix tailTrace_275289
  have hstable : (prefixWord ++ tailWord_275289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275289).length < 2 ^ (prefixWord ++ tailWord_275289).sum := by decide
  have hdescent : baseEnd_275289 < baseStart_275289 := by decide
  rcases family_descends (prefixWord ++ tailWord_275289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275303 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 5]
def baseStart_275303 : Nat := 118140960795 + 275303 * 2 ^ 59
def prefixEnd_275303 : Nat := 4983230072969 + 3 ^ 40 * 275303 * 2
def baseEnd_275303 : Nat := 125655790777636986174587

theorem tailTrace_275303 : CollatzResearch.WordTrace tailWord_275303 prefixEnd_275303 125655790777636986174587 := by
  unfold tailWord_275303
  simp only [CollatzResearch.WordTrace]
  refine ⟨10041125321631723854214563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6694083547754482569476375 10041125321631723854214563)
  ·
    refine ⟨15061687982447585781321845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10041125321631723854214563 15061687982447585781321845)
    ·
      refine ⟨1412033248354461166998923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15061687982447585781321845 1412033248354461166998923)
      ·
        refine ⟨2118049872531691750498385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412033248354461166998923 2118049872531691750498385)
        ·
          refine ⟨1588537404398768812873789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2118049872531691750498385 1588537404398768812873789)
          ·
            refine ⟨595701526649538304827671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1588537404398768812873789 595701526649538304827671)
            ·
              refine ⟨893552289974307457241507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595701526649538304827671 893552289974307457241507)
              ·
                refine ⟨1340328434961461185862261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893552289974307457241507 1340328434961461185862261)
                ·
                  refine ⟨125655790777636986174587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1340328434961461185862261 125655790777636986174587)
                  ·
                    rfl

theorem cell20_275303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_275303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275303 prefixEnd_275303 := by exact prefixLift 275303
  have htrace : WordTrace (prefixWord ++ tailWord_275303) baseStart_275303 baseEnd_275303 := by
    simpa [prefixWord, tailWord_275303, baseEnd_275303] using wordTrace_append hprefix tailTrace_275303
  have hstable : (prefixWord ++ tailWord_275303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275303).length < 2 ^ (prefixWord ++ tailWord_275303).sum := by decide
  have hdescent : baseEnd_275303 < baseStart_275303 := by decide
  rcases family_descends (prefixWord ++ tailWord_275303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275330 : List Nat := [3, 4, 2, 2, 1, 1, 1, 6]
def baseStart_275330 : Nat := 118140960795 + 275330 * 2 ^ 59
def prefixEnd_275330 : Nat := 4983230072969 + 3 ^ 40 * 275330 * 2
def baseEnd_275330 : Nat := 41889371437781630758159

theorem tailTrace_275330 : CollatzResearch.WordTrace tailWord_275330 prefixEnd_275330 41889371437781630758159 := by
  unfold tailWord_275330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510527523133476866361861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6694740061689271643631629 2510527523133476866361861)
  ·
    refine ⟨470723910587526912442849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2510527523133476866361861 470723910587526912442849)
    ·
      refine ⟨353042932940645184332137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 470723910587526912442849 353042932940645184332137)
      ·
        refine ⟨264782199705483888249103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353042932940645184332137 264782199705483888249103)
        ·
          refine ⟨397173299558225832373655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264782199705483888249103 397173299558225832373655)
          ·
            refine ⟨595759949337338748560483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397173299558225832373655 595759949337338748560483)
            ·
              refine ⟨893639924006008122840725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595759949337338748560483 893639924006008122840725)
              ·
                refine ⟨41889371437781630758159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 893639924006008122840725 41889371437781630758159)
                ·
                  rfl

theorem cell20_275330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_275330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275330 prefixEnd_275330 := by exact prefixLift 275330
  have htrace : WordTrace (prefixWord ++ tailWord_275330) baseStart_275330 baseEnd_275330 := by
    simpa [prefixWord, tailWord_275330, baseEnd_275330] using wordTrace_append hprefix tailTrace_275330
  have hstable : (prefixWord ++ tailWord_275330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275330).length < 2 ^ (prefixWord ++ tailWord_275330).sum := by decide
  have hdescent : baseEnd_275330 < baseStart_275330 := by decide
  rcases family_descends (prefixWord ++ tailWord_275330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275361 : List Nat := [1, 2, 3, 4, 1, 2, 3, 2, 2]
def baseStart_275361 : Nat := 118140960795 + 275361 * 2 ^ 59
def prefixEnd_275361 : Nat := 4983230072969 + 3 ^ 40 * 275361 * 2
def baseEnd_275361 : Nat := 125682263558046562241017

theorem tailTrace_275361 : CollatzResearch.WordTrace tailWord_275361 prefixEnd_275361 125682263558046562241017 := by
  unfold tailWord_275361
  simp only [CollatzResearch.WordTrace]
  refine ⟨10043240755421599759825937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6695493836947733173217291 10043240755421599759825937)
  ·
    refine ⟨7532430566566199819869453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10043240755421599759825937 7532430566566199819869453)
    ·
      refine ⟨2824661462462324932451045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7532430566566199819869453 2824661462462324932451045)
      ·
        refine ⟨529624024211685924834571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2824661462462324932451045 529624024211685924834571)
        ·
          refine ⟨794436036317528887251857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529624024211685924834571 794436036317528887251857)
          ·
            refine ⟨595827027238146665438893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794436036317528887251857 595827027238146665438893)
            ·
              refine ⟨223435135214304999539585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 595827027238146665438893 223435135214304999539585)
              ·
                refine ⟨167576351410728749654689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223435135214304999539585 167576351410728749654689)
                ·
                  refine ⟨125682263558046562241017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167576351410728749654689 125682263558046562241017)
                  ·
                    rfl

theorem cell20_275361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_275361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275361 prefixEnd_275361 := by exact prefixLift 275361
  have htrace : WordTrace (prefixWord ++ tailWord_275361) baseStart_275361 baseEnd_275361 := by
    simpa [prefixWord, tailWord_275361, baseEnd_275361] using wordTrace_append hprefix tailTrace_275361
  have hstable : (prefixWord ++ tailWord_275361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275361).length < 2 ^ (prefixWord ++ tailWord_275361).sum := by decide
  have hdescent : baseEnd_275361 < baseStart_275361 := by decide
  rcases family_descends (prefixWord ++ tailWord_275361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275417 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 3]
def baseStart_275417 : Nat := 118140960795 + 275417 * 2 ^ 59
def prefixEnd_275417 : Nat := 4983230072969 + 3 ^ 40 * 275417 * 2
def baseEnd_275417 : Nat := 125707823483959256374121

theorem tailTrace_275417 : CollatzResearch.WordTrace tailWord_275417 prefixEnd_275417 125707823483959256374121 := by
  unfold tailWord_275417
  simp only [CollatzResearch.WordTrace]
  refine ⟨10045283243218721323864505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6696855495479147549243003 10045283243218721323864505)
  ·
    refine ⟨7533962432414040992898379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10045283243218721323864505 7533962432414040992898379)
    ·
      refine ⟨11300943648621061489347569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7533962432414040992898379 11300943648621061489347569)
      ·
        refine ⟨8475707736465796117010677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11300943648621061489347569 8475707736465796117010677)
        ·
          refine ⟨794597600293668385969751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8475707736465796117010677 794597600293668385969751)
          ·
            refine ⟨1191896400440502578954627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794597600293668385969751 1191896400440502578954627)
            ·
              refine ⟨1787844600660753868431941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191896400440502578954627 1787844600660753868431941)
              ·
                refine ⟨335220862623891350330989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1787844600660753868431941 335220862623891350330989)
                ·
                  refine ⟨125707823483959256374121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335220862623891350330989 125707823483959256374121)
                  ·
                    rfl

theorem cell20_275417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_275417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275417 prefixEnd_275417 := by exact prefixLift 275417
  have htrace : WordTrace (prefixWord ++ tailWord_275417) baseStart_275417 baseEnd_275417 := by
    simpa [prefixWord, tailWord_275417, baseEnd_275417] using wordTrace_append hprefix tailTrace_275417
  have hstable : (prefixWord ++ tailWord_275417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275417).length < 2 ^ (prefixWord ++ tailWord_275417).sum := by decide
  have hdescent : baseEnd_275417 < baseStart_275417 := by decide
  rcases family_descends (prefixWord ++ tailWord_275417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275479 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 4]
def baseStart_275479 : Nat := 118140960795 + 275479 * 2 ^ 59
def prefixEnd_275479 : Nat := 4983230072969 + 3 ^ 40 * 275479 * 2
def baseEnd_275479 : Nat := 125736121973362596307201

theorem tailTrace_275479 : CollatzResearch.WordTrace tailWord_275479 prefixEnd_275479 125736121973362596307201 := by
  unfold tailWord_275479
  simp only [CollatzResearch.WordTrace]
  refine ⟨10047544568994105912621491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6698363045996070608414327 10047544568994105912621491)
  ·
    refine ⟨15071316853491158868932237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10047544568994105912621491 15071316853491158868932237)
    ·
      refine ⟨5651743820059184575849589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15071316853491158868932237 5651743820059184575849589)
      ·
        refine ⟨529850983130548553985899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5651743820059184575849589 529850983130548553985899)
        ·
          refine ⟨794776474695822830978849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529850983130548553985899 794776474695822830978849)
          ·
            refine ⟨596082356021867123234137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794776474695822830978849 596082356021867123234137)
            ·
              refine ⟨447061767016400342425603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596082356021867123234137 447061767016400342425603)
              ·
                refine ⟨670592650524600513638405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447061767016400342425603 670592650524600513638405)
                ·
                  refine ⟨125736121973362596307201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670592650524600513638405 125736121973362596307201)
                  ·
                    rfl

theorem cell20_275479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_275479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275479 prefixEnd_275479 := by exact prefixLift 275479
  have htrace : WordTrace (prefixWord ++ tailWord_275479) baseStart_275479 baseEnd_275479 := by
    simpa [prefixWord, tailWord_275479, baseEnd_275479] using wordTrace_append hprefix tailTrace_275479
  have hstable : (prefixWord ++ tailWord_275479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275479).length < 2 ^ (prefixWord ++ tailWord_275479).sum := by decide
  have hdescent : baseEnd_275479 < baseStart_275479 := by decide
  rcases family_descends (prefixWord ++ tailWord_275479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275514 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_275514 : Nat := 118140960795 + 275514 * 2 ^ 59
def prefixEnd_275514 : Nat := 4983230072969 + 3 ^ 40 * 275514 * 2
def baseEnd_275514 : Nat := 125752096927058030140391

theorem tailTrace_275514 : CollatzResearch.WordTrace tailWord_275514 prefixEnd_275514 125752096927058030140391 := by
  unfold tailWord_275514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2512205280966826722536399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6699214082578204593430397 2512205280966826722536399)
  ·
    refine ⟨3768307921450240083804599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2512205280966826722536399 3768307921450240083804599)
    ·
      refine ⟨5652461882175360125706899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3768307921450240083804599 5652461882175360125706899)
      ·
        refine ⟨8478692823263040188560349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5652461882175360125706899 8478692823263040188560349)
        ·
          refine ⟨3179509808723640070710131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8478692823263040188560349 3179509808723640070710131)
          ·
            refine ⟨4769264713085460106065197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179509808723640070710131 4769264713085460106065197)
            ·
              refine ⟨1788474267407047539774449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4769264713085460106065197 1788474267407047539774449)
              ·
                refine ⟨1341355700555285654830837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788474267407047539774449 1341355700555285654830837)
                ·
                  refine ⟨125752096927058030140391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1341355700555285654830837 125752096927058030140391)
                  ·
                    rfl

theorem cell20_275514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_275514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275514 prefixEnd_275514 := by exact prefixLift 275514
  have htrace : WordTrace (prefixWord ++ tailWord_275514) baseStart_275514 baseEnd_275514 := by
    simpa [prefixWord, tailWord_275514, baseEnd_275514] using wordTrace_append hprefix tailTrace_275514
  have hstable : (prefixWord ++ tailWord_275514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275514).length < 2 ^ (prefixWord ++ tailWord_275514).sum := by decide
  have hdescent : baseEnd_275514 < baseStart_275514 := by decide
  rcases family_descends (prefixWord ++ tailWord_275514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275534 : List Nat := [4, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_275534 : Nat := 118140960795 + 275534 * 2 ^ 59
def prefixEnd_275534 : Nat := 4983230072969 + 3 ^ 40 * 275534 * 2
def baseEnd_275534 : Nat := 125761225472026849473643

theorem tailTrace_275534 : CollatzResearch.WordTrace tailWord_275534 prefixEnd_275534 125761225472026849473643 := by
  unfold tailWord_275534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1256193822974356288234207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6699700389196566870582437 1256193822974356288234207)
  ·
    refine ⟨1884290734461534432351311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1256193822974356288234207 1884290734461534432351311)
    ·
      refine ⟨2826436101692301648526967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1884290734461534432351311 2826436101692301648526967)
      ·
        refine ⟨4239654152538452472790451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2826436101692301648526967 4239654152538452472790451)
        ·
          refine ⟨6359481228807678709185677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4239654152538452472790451 6359481228807678709185677)
          ·
            refine ⟨2384805460802879515944629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6359481228807678709185677 2384805460802879515944629)
            ·
              refine ⟨223575511950269954619809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2384805460802879515944629 223575511950269954619809)
              ·
                refine ⟨167681633962702465964857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223575511950269954619809 167681633962702465964857)
                ·
                  refine ⟨125761225472026849473643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167681633962702465964857 125761225472026849473643)
                  ·
                    rfl

theorem cell20_275534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_275534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275534 prefixEnd_275534 := by exact prefixLift 275534
  have htrace : WordTrace (prefixWord ++ tailWord_275534) baseStart_275534 baseEnd_275534 := by
    simpa [prefixWord, tailWord_275534, baseEnd_275534] using wordTrace_append hprefix tailTrace_275534
  have hstable : (prefixWord ++ tailWord_275534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275534).length < 2 ^ (prefixWord ++ tailWord_275534).sum := by decide
  have hdescent : baseEnd_275534 < baseStart_275534 := by decide
  rcases family_descends (prefixWord ++ tailWord_275534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275589 : List Nat := [1, 3, 1, 1, 6, 2, 2, 2, 2]
def baseStart_275589 : Nat := 118140960795 + 275589 * 2 ^ 59
def prefixEnd_275589 : Nat := 4983230072969 + 3 ^ 40 * 275589 * 2
def baseEnd_275589 : Nat := 125786328970691102640085

theorem tailTrace_275589 : CollatzResearch.WordTrace tailWord_275589 prefixEnd_275589 125786328970691102640085 := by
  unfold tailWord_275589
  simp only [CollatzResearch.WordTrace]
  refine ⟨10051556598595594699125821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6701037732397063132750547 10051556598595594699125821)
  ·
    refine ⟨3769333724473348012172183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10051556598595594699125821 3769333724473348012172183)
    ·
      refine ⟨5654000586710022018258275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3769333724473348012172183 5654000586710022018258275)
      ·
        refine ⟨8481000880065033027387413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5654000586710022018258275 8481000880065033027387413)
        ·
          refine ⟨397546916253048423158785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8481000880065033027387413 397546916253048423158785)
          ·
            refine ⟨298160187189786317369089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397546916253048423158785 298160187189786317369089)
            ·
              refine ⟨223620140392339738026817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298160187189786317369089 223620140392339738026817)
              ·
                refine ⟨167715105294254803520113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223620140392339738026817 167715105294254803520113)
                ·
                  refine ⟨125786328970691102640085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167715105294254803520113 125786328970691102640085)
                  ·
                    rfl

theorem cell20_275589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_275589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275589 prefixEnd_275589 := by exact prefixLift 275589
  have htrace : WordTrace (prefixWord ++ tailWord_275589) baseStart_275589 baseEnd_275589 := by
    simpa [prefixWord, tailWord_275589, baseEnd_275589] using wordTrace_append hprefix tailTrace_275589
  have hstable : (prefixWord ++ tailWord_275589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275589).length < 2 ^ (prefixWord ++ tailWord_275589).sum := by decide
  have hdescent : baseEnd_275589 < baseStart_275589 := by decide
  rcases family_descends (prefixWord ++ tailWord_275589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275593 : List Nat := [1, 2, 1, 1, 4, 4, 1, 4, 2]
def baseStart_275593 : Nat := 118140960795 + 275593 * 2 ^ 59
def prefixEnd_275593 : Nat := 4983230072969 + 3 ^ 40 * 275593 * 2
def baseEnd_275593 : Nat := 125788154679684866506735

theorem tailTrace_275593 : CollatzResearch.WordTrace tailWord_275593 prefixEnd_275593 125788154679684866506735 := by
  unfold tailWord_275593
  simp only [CollatzResearch.WordTrace]
  refine ⟨10051702490581103382271433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6701134993720735588180955 10051702490581103382271433)
  ·
    refine ⟨7538776867935827536703575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10051702490581103382271433 7538776867935827536703575)
    ·
      refine ⟨11308165301903741305055363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7538776867935827536703575 11308165301903741305055363)
      ·
        refine ⟨16962247952855611957583045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11308165301903741305055363 16962247952855611957583045)
        ·
          refine ⟨3180421491160427242046821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16962247952855611957583045 3180421491160427242046821)
          ·
            refine ⟨596329029592580107883779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3180421491160427242046821 596329029592580107883779)
            ·
              refine ⟨894493544388870161825669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596329029592580107883779 894493544388870161825669)
              ·
                refine ⟨167717539572913155342313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 894493544388870161825669 167717539572913155342313)
                ·
                  refine ⟨125788154679684866506735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167717539572913155342313 125788154679684866506735)
                  ·
                    rfl

theorem cell20_275593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_275593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275593 prefixEnd_275593 := by exact prefixLift 275593
  have htrace : WordTrace (prefixWord ++ tailWord_275593) baseStart_275593 baseEnd_275593 := by
    simpa [prefixWord, tailWord_275593, baseEnd_275593] using wordTrace_append hprefix tailTrace_275593
  have hstable : (prefixWord ++ tailWord_275593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275593).length < 2 ^ (prefixWord ++ tailWord_275593).sum := by decide
  have hdescent : baseEnd_275593 < baseStart_275593 := by decide
  rcases family_descends (prefixWord ++ tailWord_275593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275607 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 3]
def baseStart_275607 : Nat := 118140960795 + 275607 * 2 ^ 59
def prefixEnd_275607 : Nat := 4983230072969 + 3 ^ 40 * 275607 * 2
def baseEnd_275607 : Nat := 125794544661163040040011

theorem tailTrace_275607 : CollatzResearch.WordTrace tailWord_275607 prefixEnd_275607 125794544661163040040011 := by
  unfold tailWord_275607
  simp only [CollatzResearch.WordTrace]
  refine ⟨10052213112530383773281075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6701475408353589182187383 10052213112530383773281075)
  ·
    refine ⟨15078319668795575659921613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10052213112530383773281075 15078319668795575659921613)
    ·
      refine ⟨5654369875798340872470605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15078319668795575659921613 5654369875798340872470605)
      ·
        refine ⟨2120388703424377827176477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5654369875798340872470605 2120388703424377827176477)
        ·
          refine ⟨795145763784141685191179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2120388703424377827176477 795145763784141685191179)
          ·
            refine ⟨1192718645676212527786769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795145763784141685191179 1192718645676212527786769)
            ·
              refine ⟨894538984257159395840077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192718645676212527786769 894538984257159395840077)
              ·
                refine ⟨335452119096434773440029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 894538984257159395840077 335452119096434773440029)
                ·
                  refine ⟨125794544661163040040011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335452119096434773440029 125794544661163040040011)
                  ·
                    rfl

theorem cell20_275607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 3].length) (baseStart_275607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275607 prefixEnd_275607 := by exact prefixLift 275607
  have htrace : WordTrace (prefixWord ++ tailWord_275607) baseStart_275607 baseEnd_275607 := by
    simpa [prefixWord, tailWord_275607, baseEnd_275607] using wordTrace_append hprefix tailTrace_275607
  have hstable : (prefixWord ++ tailWord_275607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275607).length < 2 ^ (prefixWord ++ tailWord_275607).sum := by decide
  have hdescent : baseEnd_275607 < baseStart_275607 := by decide
  rcases family_descends (prefixWord ++ tailWord_275607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275645 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 3]
def baseStart_275645 : Nat := 118140960795 + 275645 * 2 ^ 59
def prefixEnd_275645 : Nat := 4983230072969 + 3 ^ 40 * 275645 * 2
def baseEnd_275645 : Nat := 125811888896603796773189

theorem tailTrace_275645 : CollatzResearch.WordTrace tailWord_275645 prefixEnd_275645 125811888896603796773189 := by
  unfold tailWord_275645
  simp only [CollatzResearch.WordTrace]
  refine ⟨10053599086392716263164389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6702399390928477508776259 10053599086392716263164389)
  ·
    refine ⟨1885049828698634299343323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10053599086392716263164389 1885049828698634299343323)
    ·
      refine ⟨2827574743047951449014985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885049828698634299343323 2827574743047951449014985)
      ·
        refine ⟨2120681057285963586761239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2827574743047951449014985 2120681057285963586761239)
        ·
          refine ⟨3181021585928945380141859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2120681057285963586761239 3181021585928945380141859)
          ·
            refine ⟨4771532378893418070212789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181021585928945380141859 4771532378893418070212789)
            ·
              refine ⟨447331160521257944082449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4771532378893418070212789 447331160521257944082449)
              ·
                refine ⟨335498370390943458061837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447331160521257944082449 335498370390943458061837)
                ·
                  refine ⟨125811888896603796773189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335498370390943458061837 125811888896603796773189)
                  ·
                    rfl

theorem cell20_275645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_275645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275645 prefixEnd_275645 := by exact prefixLift 275645
  have htrace : WordTrace (prefixWord ++ tailWord_275645) baseStart_275645 baseEnd_275645 := by
    simpa [prefixWord, tailWord_275645, baseEnd_275645] using wordTrace_append hprefix tailTrace_275645
  have hstable : (prefixWord ++ tailWord_275645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275645).length < 2 ^ (prefixWord ++ tailWord_275645).sum := by decide
  have hdescent : baseEnd_275645 < baseStart_275645 := by decide
  rcases family_descends (prefixWord ++ tailWord_275645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275762 : List Nat := [3, 2, 1, 1, 4, 1, 4, 2, 2]
def baseStart_275762 : Nat := 118140960795 + 275762 * 2 ^ 59
def prefixEnd_275762 : Nat := 4983230072969 + 3 ^ 40 * 275762 * 2
def baseEnd_275762 : Nat := 125865290884671389872711

theorem tailTrace_275762 : CollatzResearch.WordTrace tailWord_275762 prefixEnd_275762 125865290884671389872711 := by
  unfold tailWord_275762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2514466606742211311293385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6705244284645896830115693 2514466606742211311293385)
  ·
    refine ⟨1885849955056658483470039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2514466606742211311293385 1885849955056658483470039)
    ·
      refine ⟨2828774932584987725205059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885849955056658483470039 2828774932584987725205059)
      ·
        refine ⟨4243162398877481587807589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2828774932584987725205059 4243162398877481587807589)
        ·
          refine ⟨795592949789527797713923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4243162398877481587807589 795592949789527797713923)
          ·
            refine ⟨1193389424684291696570885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795592949789527797713923 1193389424684291696570885)
            ·
              refine ⟨223760517128304693107041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1193389424684291696570885 223760517128304693107041)
              ·
                refine ⟨167820387846228519830281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223760517128304693107041 167820387846228519830281)
                ·
                  refine ⟨125865290884671389872711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167820387846228519830281 125865290884671389872711)
                  ·
                    rfl

theorem cell20_275762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_275762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275762 prefixEnd_275762 := by exact prefixLift 275762
  have htrace : WordTrace (prefixWord ++ tailWord_275762) baseStart_275762 baseEnd_275762 := by
    simpa [prefixWord, tailWord_275762, baseEnd_275762] using wordTrace_append hprefix tailTrace_275762
  have hstable : (prefixWord ++ tailWord_275762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275762).length < 2 ^ (prefixWord ++ tailWord_275762).sum := by decide
  have hdescent : baseEnd_275762 < baseStart_275762 := by decide
  rcases family_descends (prefixWord ++ tailWord_275762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275769 : List Nat := [1, 2, 1, 6, 3, 1, 1, 5]
def baseStart_275769 : Nat := 118140960795 + 275769 * 2 ^ 59
def prefixEnd_275769 : Nat := 4983230072969 + 3 ^ 40 * 275769 * 2
def baseEnd_275769 : Nat := 41956161958470158879783

theorem tailTrace_275769 : CollatzResearch.WordTrace tailWord_275769 prefixEnd_275769 41956161958470158879783 := by
  unfold tailWord_275769
  simp only [CollatzResearch.WordTrace]
  refine ⟨10058121737943485440678361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6705414491962323627118907 10058121737943485440678361)
  ·
    refine ⟨7543591303457614080508771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10058121737943485440678361 7543591303457614080508771)
    ·
      refine ⟨11315386955186421120763157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7543591303457614080508771 11315386955186421120763157)
      ·
        refine ⟨530408763524363490035773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11315386955186421120763157 530408763524363490035773)
        ·
          refine ⟨198903286321636308763415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 530408763524363490035773 198903286321636308763415)
          ·
            refine ⟨298354929482454463145123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198903286321636308763415 298354929482454463145123)
            ·
              refine ⟨447532394223681694717685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298354929482454463145123 447532394223681694717685)
              ·
                refine ⟨41956161958470158879783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 447532394223681694717685 41956161958470158879783)
                ·
                  rfl

theorem cell20_275769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 5].length) (baseStart_275769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275769 prefixEnd_275769 := by exact prefixLift 275769
  have htrace : WordTrace (prefixWord ++ tailWord_275769) baseStart_275769 baseEnd_275769 := by
    simpa [prefixWord, tailWord_275769, baseEnd_275769] using wordTrace_append hprefix tailTrace_275769
  have hstable : (prefixWord ++ tailWord_275769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275769).length < 2 ^ (prefixWord ++ tailWord_275769).sum := by decide
  have hdescent : baseEnd_275769 < baseStart_275769 := by decide
  rcases family_descends (prefixWord ++ tailWord_275769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275821 : List Nat := [1, 5, 1, 1, 1, 3, 2, 4, 2]
def baseStart_275821 : Nat := 118140960795 + 275821 * 2 ^ 59
def prefixEnd_275821 : Nat := 4983230072969 + 3 ^ 40 * 275821 * 2
def baseEnd_275821 : Nat := 125892220092329406905803

theorem tailTrace_275821 : CollatzResearch.WordTrace tailWord_275821 prefixEnd_275821 125892220092329406905803 := by
  unfold tailWord_275821
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060018333755098321571317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6706678889170065547714211 10060018333755098321571317)
  ·
    refine ⟨943126718789540467647311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10060018333755098321571317 943126718789540467647311)
    ·
      refine ⟨1414690078184310701470967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 943126718789540467647311 1414690078184310701470967)
      ·
        refine ⟨2122035117276466052206451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414690078184310701470967 2122035117276466052206451)
        ·
          refine ⟨3183052675914699078309677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2122035117276466052206451 3183052675914699078309677)
          ·
            refine ⟨1193644753468012154366129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3183052675914699078309677 1193644753468012154366129)
            ·
              refine ⟨895233565101009115774597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193644753468012154366129 895233565101009115774597)
              ·
                refine ⟨167856293456439209207737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 895233565101009115774597 167856293456439209207737)
                ·
                  refine ⟨125892220092329406905803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167856293456439209207737 125892220092329406905803)
                  ·
                    rfl

theorem cell20_275821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_275821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275821 prefixEnd_275821 := by exact prefixLift 275821
  have htrace : WordTrace (prefixWord ++ tailWord_275821) baseStart_275821 baseEnd_275821 := by
    simpa [prefixWord, tailWord_275821, baseEnd_275821] using wordTrace_append hprefix tailTrace_275821
  have hstable : (prefixWord ++ tailWord_275821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275821).length < 2 ^ (prefixWord ++ tailWord_275821).sum := by decide
  have hdescent : baseEnd_275821 < baseStart_275821 := by decide
  rcases family_descends (prefixWord ++ tailWord_275821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275825 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_275825 : Nat := 118140960795 + 275825 * 2 ^ 59
def prefixEnd_275825 : Nat := 4983230072969 + 3 ^ 40 * 275825 * 2
def baseEnd_275825 : Nat := 125894045801323170772453

theorem tailTrace_275825 : CollatzResearch.WordTrace tailWord_275825 prefixEnd_275825 125894045801323170772453 := by
  unfold tailWord_275825
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060164225740607004716929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6706776150493738003144619 10060164225740607004716929)
  ·
    refine ⟨7545123169305455253537697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10060164225740607004716929 7545123169305455253537697)
    ·
      refine ⟨5658842376979091440153273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7545123169305455253537697 5658842376979091440153273)
      ·
        refine ⟨4244131782734318580114955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5658842376979091440153273 4244131782734318580114955)
        ·
          refine ⟨6366197674101477870172433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244131782734318580114955 6366197674101477870172433)
          ·
            refine ⟨4774648255576108402629325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6366197674101477870172433 4774648255576108402629325)
            ·
              refine ⟨1790493095841040650985997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4774648255576108402629325 1790493095841040650985997)
              ·
                refine ⟨671434910940390244119749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1790493095841040650985997 671434910940390244119749)
                ·
                  refine ⟨125894045801323170772453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 671434910940390244119749 125894045801323170772453)
                  ·
                    rfl

theorem cell20_275825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_275825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275825 prefixEnd_275825 := by exact prefixLift 275825
  have htrace : WordTrace (prefixWord ++ tailWord_275825) baseStart_275825 baseEnd_275825 := by
    simpa [prefixWord, tailWord_275825, baseEnd_275825] using wordTrace_append hprefix tailTrace_275825
  have hstable : (prefixWord ++ tailWord_275825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275825).length < 2 ^ (prefixWord ++ tailWord_275825).sum := by decide
  have hdescent : baseEnd_275825 < baseStart_275825 := by decide
  rcases family_descends (prefixWord ++ tailWord_275825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275835 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 3]
def baseStart_275835 : Nat := 118140960795 + 275835 * 2 ^ 59
def prefixEnd_275835 : Nat := 4983230072969 + 3 ^ 40 * 275835 * 2
def baseEnd_275835 : Nat := 125898610073807580439079

theorem tailTrace_275835 : CollatzResearch.WordTrace tailWord_275835 prefixEnd_275835 125898610073807580439079 := by
  unfold tailWord_275835
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060528955704378712580959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6707019303802919141720639 10060528955704378712580959)
  ·
    refine ⟨15090793433556568068871439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10060528955704378712580959 15090793433556568068871439)
    ·
      refine ⟨22636190150334852103307159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15090793433556568068871439 22636190150334852103307159)
      ·
        refine ⟨33954285225502278154960739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22636190150334852103307159 33954285225502278154960739)
        ·
          refine ⟨50931427838253417232441109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33954285225502278154960739 50931427838253417232441109)
          ·
            refine ⟨2387410679918128932770677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50931427838253417232441109 2387410679918128932770677)
            ·
              refine ⟨223819751242324587447251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2387410679918128932770677 223819751242324587447251)
              ·
                refine ⟨335729626863486881170877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223819751242324587447251 335729626863486881170877)
                ·
                  refine ⟨125898610073807580439079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335729626863486881170877 125898610073807580439079)
                  ·
                    rfl

theorem cell20_275835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 3].length) (baseStart_275835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275835 prefixEnd_275835 := by exact prefixLift 275835
  have htrace : WordTrace (prefixWord ++ tailWord_275835) baseStart_275835 baseEnd_275835 := by
    simpa [prefixWord, tailWord_275835, baseEnd_275835] using wordTrace_append hprefix tailTrace_275835
  have hstable : (prefixWord ++ tailWord_275835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275835).length < 2 ^ (prefixWord ++ tailWord_275835).sum := by decide
  have hdescent : baseEnd_275835 < baseStart_275835 := by decide
  rcases family_descends (prefixWord ++ tailWord_275835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275839 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_275839 : Nat := 118140960795 + 275839 * 2 ^ 59
def prefixEnd_275839 : Nat := 4983230072969 + 3 ^ 40 * 275839 * 2
def baseEnd_275839 : Nat := 125900435782801344305729

theorem tailTrace_275839 : CollatzResearch.WordTrace tailWord_275839 prefixEnd_275839 125900435782801344305729 := by
  unfold tailWord_275839
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060674847689887395726571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6707116565126591597151047 10060674847689887395726571)
  ·
    refine ⟨15091012271534831093589857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10060674847689887395726571 15091012271534831093589857)
    ·
      refine ⟨11318259203651123320192393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15091012271534831093589857 11318259203651123320192393)
      ·
        refine ⟨8488694402738342490144295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11318259203651123320192393 8488694402738342490144295)
        ·
          refine ⟨12733041604107513735216443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8488694402738342490144295 12733041604107513735216443)
          ·
            refine ⟨19099562406161270602824665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12733041604107513735216443 19099562406161270602824665)
            ·
              refine ⟨14324671804620952952118499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19099562406161270602824665 14324671804620952952118499)
              ·
                refine ⟨21487007706931429428177749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14324671804620952952118499 21487007706931429428177749)
                ·
                  refine ⟨125900435782801344305729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21487007706931429428177749 125900435782801344305729)
                  ·
                    rfl

theorem cell20_275839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_275839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275839 prefixEnd_275839 := by exact prefixLift 275839
  have htrace : WordTrace (prefixWord ++ tailWord_275839) baseStart_275839 baseEnd_275839 := by
    simpa [prefixWord, tailWord_275839, baseEnd_275839] using wordTrace_append hprefix tailTrace_275839
  have hstable : (prefixWord ++ tailWord_275839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275839).length < 2 ^ (prefixWord ++ tailWord_275839).sum := by decide
  have hdescent : baseEnd_275839 < baseStart_275839 := by decide
  rcases family_descends (prefixWord ++ tailWord_275839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275849 : List Nat := [1, 2, 1, 1, 7, 1, 1, 6]
def baseStart_275849 : Nat := 118140960795 + 275849 * 2 ^ 59
def prefixEnd_275849 : Nat := 4983230072969 + 3 ^ 40 * 275849 * 2
def baseEnd_275849 : Nat := 41968333351761917990785

theorem tailTrace_275849 : CollatzResearch.WordTrace tailWord_275849 prefixEnd_275849 41968333351761917990785 := by
  unfold tailWord_275849
  simp only [CollatzResearch.WordTrace]
  refine ⟨10061039577653659103590601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6707359718435772735727067 10061039577653659103590601)
  ·
    refine ⟨7545779683240244327692951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10061039577653659103590601 7545779683240244327692951)
    ·
      refine ⟨11318669524860366491539427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7545779683240244327692951 11318669524860366491539427)
      ·
        refine ⟨16978004287290549737309141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11318669524860366491539427 16978004287290549737309141)
        ·
          refine ⟨397921975483372259468183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16978004287290549737309141 397921975483372259468183)
          ·
            refine ⟨596882963225058389202275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397921975483372259468183 596882963225058389202275)
            ·
              refine ⟨895324444837587583803413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596882963225058389202275 895324444837587583803413)
              ·
                refine ⟨41968333351761917990785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 895324444837587583803413 41968333351761917990785)
                ·
                  rfl

theorem cell20_275849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 6].length) (baseStart_275849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275849 prefixEnd_275849 := by exact prefixLift 275849
  have htrace : WordTrace (prefixWord ++ tailWord_275849) baseStart_275849 baseEnd_275849 := by
    simpa [prefixWord, tailWord_275849, baseEnd_275849] using wordTrace_append hprefix tailTrace_275849
  have hstable : (prefixWord ++ tailWord_275849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275849).length < 2 ^ (prefixWord ++ tailWord_275849).sum := by decide
  have hdescent : baseEnd_275849 < baseStart_275849 := by decide
  rcases family_descends (prefixWord ++ tailWord_275849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275901 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_275901 : Nat := 118140960795 + 275901 * 2 ^ 59
def prefixEnd_275901 : Nat := 4983230072969 + 3 ^ 40 * 275901 * 2
def baseEnd_275901 : Nat := 125928734272204684238809

theorem tailTrace_275901 : CollatzResearch.WordTrace tailWord_275901 prefixEnd_275901 125928734272204684238809 := by
  unfold tailWord_275901
  simp only [CollatzResearch.WordTrace]
  refine ⟨10062936173465271984483557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6708624115643514656322371 10062936173465271984483557)
  ·
    refine ⟨1886800532524738497090667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10062936173465271984483557 1886800532524738497090667)
    ·
      refine ⟨2830200798787107745636001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1886800532524738497090667 2830200798787107745636001)
      ·
        refine ⟨2122650599090330809227001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2830200798787107745636001 2122650599090330809227001)
        ·
          refine ⟨1591987949317748106920251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2122650599090330809227001 1591987949317748106920251)
          ·
            refine ⟨2387981923976622160380377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591987949317748106920251 2387981923976622160380377)
            ·
              refine ⟨1790986442982466620285283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2387981923976622160380377 1790986442982466620285283)
              ·
                refine ⟨2686479664473699930427925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790986442982466620285283 2686479664473699930427925)
                ·
                  refine ⟨125928734272204684238809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2686479664473699930427925 125928734272204684238809)
                  ·
                    rfl

theorem cell20_275901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_275901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275901 prefixEnd_275901 := by exact prefixLift 275901
  have htrace : WordTrace (prefixWord ++ tailWord_275901) baseStart_275901 baseEnd_275901 := by
    simpa [prefixWord, tailWord_275901, baseEnd_275901] using wordTrace_append hprefix tailTrace_275901
  have hstable : (prefixWord ++ tailWord_275901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275901).length < 2 ^ (prefixWord ++ tailWord_275901).sum := by decide
  have hdescent : baseEnd_275901 < baseStart_275901 := by decide
  rcases family_descends (prefixWord ++ tailWord_275901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275915 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_275915 : Nat := 118140960795 + 275915 * 2 ^ 59
def prefixEnd_275915 : Nat := 4983230072969 + 3 ^ 40 * 275915 * 2
def baseEnd_275915 : Nat := 125935124253682857772085

theorem tailTrace_275915 : CollatzResearch.WordTrace tailWord_275915 prefixEnd_275915 125935124253682857772085 := by
  unfold tailWord_275915
  simp only [CollatzResearch.WordTrace]
  refine ⟨10063446795414552375493199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6708964530276368250328799 10063446795414552375493199)
  ·
    refine ⟨15095170193121828563239799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10063446795414552375493199 15095170193121828563239799)
    ·
      refine ⟨22642755289682742844859699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15095170193121828563239799 22642755289682742844859699)
      ·
        refine ⟨33964132934524114267289549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22642755289682742844859699 33964132934524114267289549)
        ·
          refine ⟨12736549850446542850233581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33964132934524114267289549 12736549850446542850233581)
          ·
            refine ⟨4776206193917453568837593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12736549850446542850233581 4776206193917453568837593)
            ·
              refine ⟨3582154645438090176628195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4776206193917453568837593 3582154645438090176628195)
              ·
                refine ⟨5373231968157135264942293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582154645438090176628195 5373231968157135264942293)
                ·
                  refine ⟨125935124253682857772085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5373231968157135264942293 125935124253682857772085)
                  ·
                    rfl

theorem cell20_275915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_275915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275915 prefixEnd_275915 := by exact prefixLift 275915
  have htrace : WordTrace (prefixWord ++ tailWord_275915) baseStart_275915 baseEnd_275915 := by
    simpa [prefixWord, tailWord_275915, baseEnd_275915] using wordTrace_append hprefix tailTrace_275915
  have hstable : (prefixWord ++ tailWord_275915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275915).length < 2 ^ (prefixWord ++ tailWord_275915).sum := by decide
  have hdescent : baseEnd_275915 < baseStart_275915 := by decide
  rcases family_descends (prefixWord ++ tailWord_275915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275987 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 3]
def baseStart_275987 : Nat := 118140960795 + 275987 * 2 ^ 59
def prefixEnd_275987 : Nat := 4983230072969 + 3 ^ 40 * 275987 * 2
def baseEnd_275987 : Nat := 125967987015570607371791

theorem tailTrace_275987 : CollatzResearch.WordTrace tailWord_275987 prefixEnd_275987 125967987015570607371791 := by
  unfold tailWord_275987
  simp only [CollatzResearch.WordTrace]
  refine ⟨10066072851153708672114215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6710715234102472448076143 10066072851153708672114215)
  ·
    refine ⟨15099109276730563008171323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10066072851153708672114215 15099109276730563008171323)
    ·
      refine ⟨22648663915095844512256985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15099109276730563008171323 22648663915095844512256985)
      ·
        refine ⟨16986497936321883384192739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22648663915095844512256985 16986497936321883384192739)
        ·
          refine ⟨25479746904482825076289109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16986497936321883384192739 25479746904482825076289109)
          ·
            refine ⟨298590784036908106362763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 25479746904482825076289109 298590784036908106362763)
            ·
              refine ⟨447886176055362159544145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298590784036908106362763 447886176055362159544145)
              ·
                refine ⟨335914632041521619658109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447886176055362159544145 335914632041521619658109)
                ·
                  refine ⟨125967987015570607371791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335914632041521619658109 125967987015570607371791)
                  ·
                    rfl

theorem cell20_275987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 3].length) (baseStart_275987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_275987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_275987 prefixEnd_275987 := by exact prefixLift 275987
  have htrace : WordTrace (prefixWord ++ tailWord_275987) baseStart_275987 baseEnd_275987 := by
    simpa [prefixWord, tailWord_275987, baseEnd_275987] using wordTrace_append hprefix tailTrace_275987
  have hstable : (prefixWord ++ tailWord_275987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275987).length < 2 ^ (prefixWord ++ tailWord_275987).sum := by decide
  have hdescent : baseEnd_275987 < baseStart_275987 := by decide
  rcases family_descends (prefixWord ++ tailWord_275987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276028 : List Nat := [2, 2, 2, 2, 4, 2, 1, 3, 2]
def baseStart_276028 : Nat := 118140960795 + 276028 * 2 ^ 59
def prefixEnd_276028 : Nat := 4983230072969 + 3 ^ 40 * 276028 * 2
def baseEnd_276028 : Nat := 125986700532756687004957

theorem tailTrace_276028 : CollatzResearch.WordTrace tailWord_276028 prefixEnd_276028 125986700532756687004957 := by
  unfold tailWord_276028
  simp only [CollatzResearch.WordTrace]
  refine ⟨5033784122002586337178369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6711712162670115116237825 5033784122002586337178369)
  ·
    refine ⟨3775338091501939752883777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5033784122002586337178369 3775338091501939752883777)
    ·
      refine ⟨2831503568626454814662833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3775338091501939752883777 2831503568626454814662833)
      ·
        refine ⟨2123627676469841110997125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2831503568626454814662833 2123627676469841110997125)
        ·
          refine ⟨398180189338095208311961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2123627676469841110997125 398180189338095208311961)
          ·
            refine ⟨298635142003571406233971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398180189338095208311961 298635142003571406233971)
            ·
              refine ⟨447952713005357109350957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298635142003571406233971 447952713005357109350957)
              ·
                refine ⟨167982267377008916006609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 447952713005357109350957 167982267377008916006609)
                ·
                  refine ⟨125986700532756687004957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167982267377008916006609 125986700532756687004957)
                  ·
                    rfl

theorem cell20_276028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_276028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276028 prefixEnd_276028 := by exact prefixLift 276028
  have htrace : WordTrace (prefixWord ++ tailWord_276028) baseStart_276028 baseEnd_276028 := by
    simpa [prefixWord, tailWord_276028, baseEnd_276028] using wordTrace_append hprefix tailTrace_276028
  have hstable : (prefixWord ++ tailWord_276028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276028).length < 2 ^ (prefixWord ++ tailWord_276028).sum := by decide
  have hdescent : baseEnd_276028 < baseStart_276028 := by decide
  rcases family_descends (prefixWord ++ tailWord_276028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276039 : List Nat := [1, 1, 4, 1, 5, 2, 6]
def baseStart_276039 : Nat := 118140960795 + 276039 * 2 ^ 59
def prefixEnd_276039 : Nat := 4983230072969 + 3 ^ 40 * 276039 * 2
def baseEnd_276039 : Nat := 13999080136943281959805

theorem tailTrace_276039 : CollatzResearch.WordTrace tailWord_276039 prefixEnd_276039 13999080136943281959805 := by
  unfold tailWord_276039
  simp only [CollatzResearch.WordTrace]
  refine ⟨10067969446965321553007171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6711979631310214368671447 10067969446965321553007171)
  ·
    refine ⟨15101954170447982329510757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10067969446965321553007171 15101954170447982329510757)
    ·
      refine ⟨2831616406958996686783267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15101954170447982329510757 2831616406958996686783267)
      ·
        refine ⟨4247424610438495030174901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2831616406958996686783267 4247424610438495030174901)
        ·
          refine ⟨398196057228608909078897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4247424610438495030174901 398196057228608909078897)
          ·
            refine ⟨298647042921456681809173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398196057228608909078897 298647042921456681809173)
            ·
              refine ⟨13999080136943281959805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 298647042921456681809173 13999080136943281959805)
              ·
                rfl

theorem cell20_276039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 6].length) (baseStart_276039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276039 prefixEnd_276039 := by exact prefixLift 276039
  have htrace : WordTrace (prefixWord ++ tailWord_276039) baseStart_276039 baseEnd_276039 := by
    simpa [prefixWord, tailWord_276039, baseEnd_276039] using wordTrace_append hprefix tailTrace_276039
  have hstable : (prefixWord ++ tailWord_276039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276039).length < 2 ^ (prefixWord ++ tailWord_276039).sum := by decide
  have hdescent : baseEnd_276039 < baseStart_276039 := by decide
  rcases family_descends (prefixWord ++ tailWord_276039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276045 : List Nat := [1, 6, 1, 1, 3, 1, 3, 2, 2]
def baseStart_276045 : Nat := 118140960795 + 276045 * 2 ^ 59
def prefixEnd_276045 : Nat := 4983230072969 + 3 ^ 40 * 276045 * 2
def baseEnd_276045 : Nat := 125994459795980183438221

theorem tailTrace_276045 : CollatzResearch.WordTrace tailWord_276045 prefixEnd_276045 125994459795980183438221 := by
  unfold tailWord_276045
  simp only [CollatzResearch.WordTrace]
  refine ⟨10068188284943584577725589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6712125523295723051817059 10068188284943584577725589)
  ·
    refine ⟨471946325856730527080887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10068188284943584577725589 471946325856730527080887)
    ·
      refine ⟨707919488785095790621331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 471946325856730527080887 707919488785095790621331)
      ·
        refine ⟨1061879233177643685931997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707919488785095790621331 1061879233177643685931997)
        ·
          refine ⟨398204712441616382224499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1061879233177643685931997 398204712441616382224499)
          ·
            refine ⟨597307068662424573336749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398204712441616382224499 597307068662424573336749)
            ·
              refine ⟨223990150748409215001281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 597307068662424573336749 223990150748409215001281)
              ·
                refine ⟨167992613061306911250961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223990150748409215001281 167992613061306911250961)
                ·
                  refine ⟨125994459795980183438221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167992613061306911250961 125994459795980183438221)
                  ·
                    rfl

theorem cell20_276045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_276045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276045 prefixEnd_276045 := by exact prefixLift 276045
  have htrace : WordTrace (prefixWord ++ tailWord_276045) baseStart_276045 baseEnd_276045 := by
    simpa [prefixWord, tailWord_276045, baseEnd_276045] using wordTrace_append hprefix tailTrace_276045
  have hstable : (prefixWord ++ tailWord_276045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276045).length < 2 ^ (prefixWord ++ tailWord_276045).sum := by decide
  have hdescent : baseEnd_276045 < baseStart_276045 := by decide
  rcases family_descends (prefixWord ++ tailWord_276045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276046 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_276046 : Nat := 118140960795 + 276046 * 2 ^ 59
def prefixEnd_276046 : Nat := 4983230072969 + 3 ^ 40 * 276046 * 2
def baseEnd_276046 : Nat := 125994916223228624404883

theorem tailTrace_276046 : CollatzResearch.WordTrace tailWord_276046 prefixEnd_276046 125994916223228624404883 := by
  unfold tailWord_276046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258528094742495218563999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6712149838626641165674661 1258528094742495218563999)
  ·
    refine ⟨1887792142113742827845999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1258528094742495218563999 1887792142113742827845999)
    ·
      refine ⟨2831688213170614241768999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1887792142113742827845999 2831688213170614241768999)
      ·
        refine ⟨4247532319755921362653499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2831688213170614241768999 4247532319755921362653499)
        ·
          refine ⟨6371298479633882043980249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4247532319755921362653499 6371298479633882043980249)
          ·
            refine ⟨4778473859725411532985187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6371298479633882043980249 4778473859725411532985187)
            ·
              refine ⟨7167710789588117299477781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778473859725411532985187 7167710789588117299477781)
              ·
                refine ⟨335986443261942998413021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7167710789588117299477781 335986443261942998413021)
                ·
                  refine ⟨125994916223228624404883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335986443261942998413021 125994916223228624404883)
                  ·
                    rfl

theorem cell20_276046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_276046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276046 prefixEnd_276046 := by exact prefixLift 276046
  have htrace : WordTrace (prefixWord ++ tailWord_276046) baseStart_276046 baseEnd_276046 := by
    simpa [prefixWord, tailWord_276046, baseEnd_276046] using wordTrace_append hprefix tailTrace_276046
  have hstable : (prefixWord ++ tailWord_276046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276046).length < 2 ^ (prefixWord ++ tailWord_276046).sum := by decide
  have hdescent : baseEnd_276046 < baseStart_276046 := by decide
  rcases family_descends (prefixWord ++ tailWord_276046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276049 : List Nat := [1, 2, 2, 1, 3, 2, 5, 2, 2]
def baseStart_276049 : Nat := 118140960795 + 276049 * 2 ^ 59
def prefixEnd_276049 : Nat := 4983230072969 + 3 ^ 40 * 276049 * 2
def baseEnd_276049 : Nat := 125996285504973947304871

theorem tailTrace_276049 : CollatzResearch.WordTrace tailWord_276049 prefixEnd_276049 125996285504973947304871 := by
  unfold tailWord_276049
  simp only [CollatzResearch.WordTrace]
  refine ⟨10068334176929093260871201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6712222784619395507247467 10068334176929093260871201)
  ·
    refine ⟨7551250632696819945653401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10068334176929093260871201 7551250632696819945653401)
    ·
      refine ⟨5663437974522614959240051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7551250632696819945653401 5663437974522614959240051)
      ·
        refine ⟨8495156961783922438860077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5663437974522614959240051 8495156961783922438860077)
        ·
          refine ⟨3185683860668970914572529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8495156961783922438860077 3185683860668970914572529)
          ·
            refine ⟨2389262895501728185929397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3185683860668970914572529 2389262895501728185929397)
            ·
              refine ⟨223993396453287017430881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2389262895501728185929397 223993396453287017430881)
              ·
                refine ⟨167995047339965263073161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223993396453287017430881 167995047339965263073161)
                ·
                  refine ⟨125996285504973947304871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167995047339965263073161 125996285504973947304871)
                  ·
                    rfl

theorem cell20_276049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_276049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276049 prefixEnd_276049 := by exact prefixLift 276049
  have htrace : WordTrace (prefixWord ++ tailWord_276049) baseStart_276049 baseEnd_276049 := by
    simpa [prefixWord, tailWord_276049, baseEnd_276049] using wordTrace_append hprefix tailTrace_276049
  have hstable : (prefixWord ++ tailWord_276049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276049).length < 2 ^ (prefixWord ++ tailWord_276049).sum := by decide
  have hdescent : baseEnd_276049 < baseStart_276049 := by decide
  rcases family_descends (prefixWord ++ tailWord_276049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276104 : List Nat := [2, 1, 3, 5, 1, 1, 1, 4, 2]
def baseStart_276104 : Nat := 118140960795 + 276104 * 2 ^ 59
def prefixEnd_276104 : Nat := 4983230072969 + 3 ^ 40 * 276104 * 2
def baseEnd_276104 : Nat := 126021389003638200471313

theorem tailTrace_276104 : CollatzResearch.WordTrace tailWord_276104 prefixEnd_276104 126021389003638200471313 := by
  unfold tailWord_276104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035170095864918827061683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6713560127819891769415577 5035170095864918827061683)
  ·
    refine ⟨7552755143797378240592525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5035170095864918827061683 7552755143797378240592525)
    ·
      refine ⟨2832283178924016840222197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7552755143797378240592525 2832283178924016840222197)
      ·
        refine ⟨265526548024126578770831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2832283178924016840222197 265526548024126578770831)
        ·
          refine ⟨398289822036189868156247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265526548024126578770831 398289822036189868156247)
          ·
            refine ⟨597434733054284802234371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398289822036189868156247 597434733054284802234371)
            ·
              refine ⟨896152099581427203351557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597434733054284802234371 896152099581427203351557)
              ·
                refine ⟨168028518671517600628417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 896152099581427203351557 168028518671517600628417)
                ·
                  refine ⟨126021389003638200471313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168028518671517600628417 126021389003638200471313)
                  ·
                    rfl

theorem cell20_276104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_276104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276104 prefixEnd_276104 := by exact prefixLift 276104
  have htrace : WordTrace (prefixWord ++ tailWord_276104) baseStart_276104 baseEnd_276104 := by
    simpa [prefixWord, tailWord_276104, baseEnd_276104] using wordTrace_append hprefix tailTrace_276104
  have hstable : (prefixWord ++ tailWord_276104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276104).length < 2 ^ (prefixWord ++ tailWord_276104).sum := by decide
  have hdescent : baseEnd_276104 < baseStart_276104 := by decide
  rcases family_descends (prefixWord ++ tailWord_276104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276105 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_276105 : Nat := 118140960795 + 276105 * 2 ^ 59
def prefixEnd_276105 : Nat := 4983230072969 + 3 ^ 40 * 276105 * 2
def baseEnd_276105 : Nat := 126021845430886641437975

theorem tailTrace_276105 : CollatzResearch.WordTrace tailWord_276105 prefixEnd_276105 126021845430886641437975 := by
  unfold tailWord_276105
  simp only [CollatzResearch.WordTrace]
  refine ⟨10070376664726214824909769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6713584443150809883273179 10070376664726214824909769)
  ·
    refine ⟨7552782498544661118682327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10070376664726214824909769 7552782498544661118682327)
    ·
      refine ⟨11329173747816991678023491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7552782498544661118682327 11329173747816991678023491)
      ·
        refine ⟨16993760621725487517035237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11329173747816991678023491 16993760621725487517035237)
        ·
          refine ⟨3186330116573528909444107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16993760621725487517035237 3186330116573528909444107)
          ·
            refine ⟨4779495174860293364166161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3186330116573528909444107 4779495174860293364166161)
            ·
              refine ⟨3584621381145220023124621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4779495174860293364166161 3584621381145220023124621)
              ·
                refine ⟨1344233017929457508671733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3584621381145220023124621 1344233017929457508671733)
                ·
                  refine ⟨126021845430886641437975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1344233017929457508671733 126021845430886641437975)
                  ·
                    rfl

theorem cell20_276105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_276105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276105 prefixEnd_276105 := by exact prefixLift 276105
  have htrace : WordTrace (prefixWord ++ tailWord_276105) baseStart_276105 baseEnd_276105 := by
    simpa [prefixWord, tailWord_276105, baseEnd_276105] using wordTrace_append hprefix tailTrace_276105
  have hstable : (prefixWord ++ tailWord_276105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276105).length < 2 ^ (prefixWord ++ tailWord_276105).sum := by decide
  have hdescent : baseEnd_276105 < baseStart_276105 := by decide
  rcases family_descends (prefixWord ++ tailWord_276105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276108 : List Nat := [2, 2, 1, 2, 1, 1, 5, 4, 2]
def baseStart_276108 : Nat := 118140960795 + 276108 * 2 ^ 59
def prefixEnd_276108 : Nat := 4983230072969 + 3 ^ 40 * 276108 * 2
def baseEnd_276108 : Nat := 126023214712631964337963

theorem tailTrace_276108 : CollatzResearch.WordTrace tailWord_276108 prefixEnd_276108 126023214712631964337963 := by
  unfold tailWord_276108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035243041857673168634489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6713657389143564224845985 5035243041857673168634489)
  ·
    refine ⟨3776432281393254876475867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5035243041857673168634489 3776432281393254876475867)
    ·
      refine ⟨5664648422089882314713801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3776432281393254876475867 5664648422089882314713801)
      ·
        refine ⟨4248486316567411736035351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5664648422089882314713801 4248486316567411736035351)
        ·
          refine ⟨6372729474851117604053027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4248486316567411736035351 6372729474851117604053027)
          ·
            refine ⟨9559094212276676406079541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6372729474851117604053027 9559094212276676406079541)
            ·
              refine ⟨896165082400938413069957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9559094212276676406079541 896165082400938413069957)
              ·
                refine ⟨168030952950175952450617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 896165082400938413069957 168030952950175952450617)
                ·
                  refine ⟨126023214712631964337963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168030952950175952450617 126023214712631964337963)
                  ·
                    rfl

theorem cell20_276108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_276108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276108 prefixEnd_276108 := by exact prefixLift 276108
  have htrace : WordTrace (prefixWord ++ tailWord_276108) baseStart_276108 baseEnd_276108 := by
    simpa [prefixWord, tailWord_276108, baseEnd_276108] using wordTrace_append hprefix tailTrace_276108
  have hstable : (prefixWord ++ tailWord_276108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276108).length < 2 ^ (prefixWord ++ tailWord_276108).sum := by decide
  have hdescent : baseEnd_276108 < baseStart_276108 := by decide
  rcases family_descends (prefixWord ++ tailWord_276108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276112 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_276112 : Nat := 118140960795 + 276112 * 2 ^ 59
def prefixEnd_276112 : Nat := 4983230072969 + 3 ^ 40 * 276112 * 2
def baseEnd_276112 : Nat := 126025040421625728204613

theorem tailTrace_276112 : CollatzResearch.WordTrace tailWord_276112 prefixEnd_276112 126025040421625728204613 := by
  unfold tailWord_276112
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035315987850427510207295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6713754650467236680276393 5035315987850427510207295)
  ·
    refine ⟨7552973981775641265310943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5035315987850427510207295 7552973981775641265310943)
    ·
      refine ⟨11329460972663461897966415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7552973981775641265310943 11329460972663461897966415)
      ·
        refine ⟨16994191458995192846949623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11329460972663461897966415 16994191458995192846949623)
        ·
          refine ⟨25491287188492789270424435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16994191458995192846949623 25491287188492789270424435)
          ·
            refine ⟨38236930782739183905636653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25491287188492789270424435 38236930782739183905636653)
            ·
              refine ⟨14338849043527193964613745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38236930782739183905636653 14338849043527193964613745)
              ·
                refine ⟨10754136782645395473460309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14338849043527193964613745 10754136782645395473460309)
                ·
                  refine ⟨126025040421625728204613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10754136782645395473460309 126025040421625728204613)
                  ·
                    rfl

theorem cell20_276112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_276112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276112 prefixEnd_276112 := by exact prefixLift 276112
  have htrace : WordTrace (prefixWord ++ tailWord_276112) baseStart_276112 baseEnd_276112 := by
    simpa [prefixWord, tailWord_276112, baseEnd_276112] using wordTrace_append hprefix tailTrace_276112
  have hstable : (prefixWord ++ tailWord_276112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276112).length < 2 ^ (prefixWord ++ tailWord_276112).sum := by decide
  have hdescent : baseEnd_276112 < baseStart_276112 := by decide
  rcases family_descends (prefixWord ++ tailWord_276112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276129 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_276129 : Nat := 118140960795 + 276129 * 2 ^ 59
def prefixEnd_276129 : Nat := 4983230072969 + 3 ^ 40 * 276129 * 2
def baseEnd_276129 : Nat := 126032799684849224637877

theorem tailTrace_276129 : CollatzResearch.WordTrace tailWord_276129 prefixEnd_276129 126032799684849224637877 := by
  unfold tailWord_276129
  simp only [CollatzResearch.WordTrace]
  refine ⟨10071252016639266923783441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6714168011092844615855627 10071252016639266923783441)
  ·
    refine ⟨7553439012479450192837581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10071252016639266923783441 7553439012479450192837581)
    ·
      refine ⟨2832539629679793822314093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7553439012479450192837581 2832539629679793822314093)
      ·
        refine ⟨1062202361129922683367785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2832539629679793822314093 1062202361129922683367785)
        ·
          refine ⟨796651770847442012525839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1062202361129922683367785 796651770847442012525839)
          ·
            refine ⟨1194977656271163018788759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796651770847442012525839 1194977656271163018788759)
            ·
              refine ⟨1792466484406744528183139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194977656271163018788759 1792466484406744528183139)
              ·
                refine ⟨2688699726610116792274709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792466484406744528183139 2688699726610116792274709)
                ·
                  refine ⟨126032799684849224637877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2688699726610116792274709 126032799684849224637877)
                  ·
                    rfl

theorem cell20_276129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_276129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276129 prefixEnd_276129 := by exact prefixLift 276129
  have htrace : WordTrace (prefixWord ++ tailWord_276129) baseStart_276129 baseEnd_276129 := by
    simpa [prefixWord, tailWord_276129, baseEnd_276129] using wordTrace_append hprefix tailTrace_276129
  have hstable : (prefixWord ++ tailWord_276129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276129).length < 2 ^ (prefixWord ++ tailWord_276129).sum := by decide
  have hdescent : baseEnd_276129 < baseStart_276129 := by decide
  rcases family_descends (prefixWord ++ tailWord_276129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276143 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_276143 : Nat := 118140960795 + 276143 * 2 ^ 59
def prefixEnd_276143 : Nat := 4983230072969 + 3 ^ 40 * 276143 * 2
def baseEnd_276143 : Nat := 126039189666327398171153

theorem tailTrace_276143 : CollatzResearch.WordTrace tailWord_276143 prefixEnd_276143 126039189666327398171153 := by
  unfold tailWord_276143
  simp only [CollatzResearch.WordTrace]
  refine ⟨10071762638588547314793083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6714508425725698209862055 10071762638588547314793083)
  ·
    refine ⟨15107643957882820972189625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10071762638588547314793083 15107643957882820972189625)
    ·
      refine ⟨11330732968412115729142219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15107643957882820972189625 11330732968412115729142219)
      ·
        refine ⟨16996099452618173593713329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11330732968412115729142219 16996099452618173593713329)
        ·
          refine ⟨12747074589463630195284997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16996099452618173593713329 12747074589463630195284997)
          ·
            refine ⟨2390076485524430661615937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12747074589463630195284997 2390076485524430661615937)
            ·
              refine ⟨1792557364143322996211953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2390076485524430661615937 1792557364143322996211953)
              ·
                refine ⟨1344418023107492247158965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1792557364143322996211953 1344418023107492247158965)
                ·
                  refine ⟨126039189666327398171153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1344418023107492247158965 126039189666327398171153)
                  ·
                    rfl

theorem cell20_276143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_276143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276143 prefixEnd_276143 := by exact prefixLift 276143
  have htrace : WordTrace (prefixWord ++ tailWord_276143) baseStart_276143 baseEnd_276143 := by
    simpa [prefixWord, tailWord_276143, baseEnd_276143] using wordTrace_append hprefix tailTrace_276143
  have hstable : (prefixWord ++ tailWord_276143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276143).length < 2 ^ (prefixWord ++ tailWord_276143).sum := by decide
  have hdescent : baseEnd_276143 < baseStart_276143 := by decide
  rcases family_descends (prefixWord ++ tailWord_276143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276146 : List Nat := [3, 2, 1, 1, 1, 2, 3, 5, 2]
def baseStart_276146 : Nat := 118140960795 + 276146 * 2 ^ 59
def prefixEnd_276146 : Nat := 4983230072969 + 3 ^ 40 * 276146 * 2
def baseEnd_276146 : Nat := 126040558948072721071141

theorem tailTrace_276146 : CollatzResearch.WordTrace tailWord_276146 prefixEnd_276146 126040558948072721071141 := by
  unfold tailWord_276146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517968014394419706788073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6714581371718452551434861 2517968014394419706788073)
  ·
    refine ⟨1888476010795814780091055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2517968014394419706788073 1888476010795814780091055)
    ·
      refine ⟨2832714016193722170136583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1888476010795814780091055 2832714016193722170136583)
      ·
        refine ⟨4249071024290583255204875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2832714016193722170136583 4249071024290583255204875)
        ·
          refine ⟨6373606536435874882807313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4249071024290583255204875 6373606536435874882807313)
          ·
            refine ⟨4780204902326906162105485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6373606536435874882807313 4780204902326906162105485)
            ·
              refine ⟨1792576838372589810789557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4780204902326906162105485 1792576838372589810789557)
              ·
                refine ⟨168054078597430294761521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1792576838372589810789557 168054078597430294761521)
                ·
                  refine ⟨126040558948072721071141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168054078597430294761521 126040558948072721071141)
                  ·
                    rfl

theorem cell20_276146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_276146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276146 prefixEnd_276146 := by exact prefixLift 276146
  have htrace : WordTrace (prefixWord ++ tailWord_276146) baseStart_276146 baseEnd_276146 := by
    simpa [prefixWord, tailWord_276146, baseEnd_276146] using wordTrace_append hprefix tailTrace_276146
  have hstable : (prefixWord ++ tailWord_276146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276146).length < 2 ^ (prefixWord ++ tailWord_276146).sum := by decide
  have hdescent : baseEnd_276146 < baseStart_276146 := by decide
  rcases family_descends (prefixWord ++ tailWord_276146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276167 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 4]
def baseStart_276167 : Nat := 118140960795 + 276167 * 2 ^ 59
def prefixEnd_276167 : Nat := 4983230072969 + 3 ^ 40 * 276167 * 2
def baseEnd_276167 : Nat := 126050143920289981371055

theorem tailTrace_276167 : CollatzResearch.WordTrace tailWord_276167 prefixEnd_276167 126050143920289981371055 := by
  unfold tailWord_276167
  simp only [CollatzResearch.WordTrace]
  refine ⟨10072637990501599413666755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6715091993667732942444503 10072637990501599413666755)
  ·
    refine ⟨15108956985752399120500133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10072637990501599413666755 15108956985752399120500133)
    ·
      refine ⟨2832929434828574835093775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15108956985752399120500133 2832929434828574835093775)
      ·
        refine ⟨4249394152242862252640663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2832929434828574835093775 4249394152242862252640663)
        ·
          refine ⟨6374091228364293378960995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4249394152242862252640663 6374091228364293378960995)
          ·
            refine ⟨9561136842546440068441493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6374091228364293378960995 9561136842546440068441493)
            ·
              refine ⟨448178289494364378208195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9561136842546440068441493 448178289494364378208195)
              ·
                refine ⟨672267434241546567312293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448178289494364378208195 672267434241546567312293)
                ·
                  refine ⟨126050143920289981371055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 672267434241546567312293 126050143920289981371055)
                  ·
                    rfl

theorem cell20_276167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_276167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276167 prefixEnd_276167 := by exact prefixLift 276167
  have htrace : WordTrace (prefixWord ++ tailWord_276167) baseStart_276167 baseEnd_276167 := by
    simpa [prefixWord, tailWord_276167, baseEnd_276167] using wordTrace_append hprefix tailTrace_276167
  have hstable : (prefixWord ++ tailWord_276167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276167).length < 2 ^ (prefixWord ++ tailWord_276167).sum := by decide
  have hdescent : baseEnd_276167 < baseStart_276167 := by decide
  rcases family_descends (prefixWord ++ tailWord_276167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276173 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 3]
def baseStart_276173 : Nat := 118140960795 + 276173 * 2 ^ 59
def prefixEnd_276173 : Nat := 4983230072969 + 3 ^ 40 * 276173 * 2
def baseEnd_276173 : Nat := 126052882483780627171031

theorem tailTrace_276173 : CollatzResearch.WordTrace tailWord_276173 prefixEnd_276173 126052882483780627171031 := by
  unfold tailWord_276173
  simp only [CollatzResearch.WordTrace]
  refine ⟨10072856828479862438385173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6715237885653241625590115 10072856828479862438385173)
  ·
    refine ⟨472165163834993551799305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10072856828479862438385173 472165163834993551799305)
    ·
      refine ⟨354123872876245163849479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 472165163834993551799305 354123872876245163849479)
      ·
        refine ⟨531185809314367745774219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354123872876245163849479 531185809314367745774219)
        ·
          refine ⟨796778713971551618661329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531185809314367745774219 796778713971551618661329)
          ·
            refine ⟨597584035478663713995997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 796778713971551618661329 597584035478663713995997)
            ·
              refine ⟨224094013304498892748499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 597584035478663713995997 224094013304498892748499)
              ·
                refine ⟨336141019956748339122749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224094013304498892748499 336141019956748339122749)
                ·
                  refine ⟨126052882483780627171031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336141019956748339122749 126052882483780627171031)
                  ·
                    rfl

theorem cell20_276173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_276173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276173 prefixEnd_276173 := by exact prefixLift 276173
  have htrace : WordTrace (prefixWord ++ tailWord_276173) baseStart_276173 baseEnd_276173 := by
    simpa [prefixWord, tailWord_276173, baseEnd_276173] using wordTrace_append hprefix tailTrace_276173
  have hstable : (prefixWord ++ tailWord_276173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276173).length < 2 ^ (prefixWord ++ tailWord_276173).sum := by decide
  have hdescent : baseEnd_276173 < baseStart_276173 := by decide
  rcases family_descends (prefixWord ++ tailWord_276173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276174 : List Nat := [4, 1, 1, 1, 3, 1, 2, 7]
def baseStart_276174 : Nat := 118140960795 + 276174 * 2 ^ 59
def prefixEnd_276174 : Nat := 4983230072969 + 3 ^ 40 * 276174 * 2
def baseEnd_276174 : Nat := 42017779637009689379231

theorem tailTrace_276174 : CollatzResearch.WordTrace tailWord_276174 prefixEnd_276174 42017779637009689379231 := by
  unfold tailWord_276174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259111662684529951146447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6715262200984159739447717 1259111662684529951146447)
  ·
    refine ⟨1888667494026794926719671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1259111662684529951146447 1888667494026794926719671)
    ·
      refine ⟨2833001241040192390079507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1888667494026794926719671 2833001241040192390079507)
      ·
        refine ⟨4249501861560288585119261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2833001241040192390079507 4249501861560288585119261)
        ·
          refine ⟨1593563198085108219419723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4249501861560288585119261 1593563198085108219419723)
          ·
            refine ⟨2390344797127662329129585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593563198085108219419723 2390344797127662329129585)
            ·
              refine ⟨1792758597845746746847189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2390344797127662329129585 1792758597845746746847189)
              ·
                refine ⟨42017779637009689379231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1792758597845746746847189 42017779637009689379231)
                ·
                  rfl

theorem cell20_276174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_276174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276174 prefixEnd_276174 := by exact prefixLift 276174
  have htrace : WordTrace (prefixWord ++ tailWord_276174) baseStart_276174 baseEnd_276174 := by
    simpa [prefixWord, tailWord_276174, baseEnd_276174] using wordTrace_append hprefix tailTrace_276174
  have hstable : (prefixWord ++ tailWord_276174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276174).length < 2 ^ (prefixWord ++ tailWord_276174).sum := by decide
  have hdescent : baseEnd_276174 < baseStart_276174 := by decide
  rcases family_descends (prefixWord ++ tailWord_276174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276177 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 3]
def baseStart_276177 : Nat := 118140960795 + 276177 * 2 ^ 59
def prefixEnd_276177 : Nat := 4983230072969 + 3 ^ 40 * 276177 * 2
def baseEnd_276177 : Nat := 126054708192774391037681

theorem tailTrace_276177 : CollatzResearch.WordTrace tailWord_276177 prefixEnd_276177 126054708192774391037681 := by
  unfold tailWord_276177
  simp only [CollatzResearch.WordTrace]
  refine ⟨10073002720465371121530785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6715335146976914081020523 10073002720465371121530785)
  ·
    refine ⟨7554752040349028341148089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10073002720465371121530785 7554752040349028341148089)
    ·
      refine ⟨5666064030261771255861067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7554752040349028341148089 5666064030261771255861067)
      ·
        refine ⟨8499096045392656883791601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5666064030261771255861067 8499096045392656883791601)
        ·
          refine ⟨6374322034044492662843701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8499096045392656883791601 6374322034044492662843701)
          ·
            refine ⟨597592690691671187141597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6374322034044492662843701 597592690691671187141597)
            ·
              refine ⟨224097259009376695178099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 597592690691671187141597 224097259009376695178099)
              ·
                refine ⟨336145888514065042767149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224097259009376695178099 336145888514065042767149)
                ·
                  refine ⟨126054708192774391037681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336145888514065042767149 126054708192774391037681)
                  ·
                    rfl

theorem cell20_276177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_276177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276177 prefixEnd_276177 := by exact prefixLift 276177
  have htrace : WordTrace (prefixWord ++ tailWord_276177) baseStart_276177 baseEnd_276177 := by
    simpa [prefixWord, tailWord_276177, baseEnd_276177] using wordTrace_append hprefix tailTrace_276177
  have hstable : (prefixWord ++ tailWord_276177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276177).length < 2 ^ (prefixWord ++ tailWord_276177).sum := by decide
  have hdescent : baseEnd_276177 < baseStart_276177 := by decide
  rcases family_descends (prefixWord ++ tailWord_276177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276250 : List Nat := [3, 1, 1, 3, 2, 2, 2, 6]
def baseStart_276250 : Nat := 118140960795 + 276250 * 2 ^ 59
def prefixEnd_276250 : Nat := 4983230072969 + 3 ^ 40 * 276250 * 2
def baseEnd_276250 : Nat := 42029342460636860534683

theorem tailTrace_276250 : CollatzResearch.WordTrace tailWord_276250 prefixEnd_276250 42029342460636860534683 := by
  unfold tailWord_276250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2518916312300226147234551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6717110166133936392625469 2518916312300226147234551)
  ·
    refine ⟨3778374468450339220851827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2518916312300226147234551 3778374468450339220851827)
    ·
      refine ⟨5667561702675508831277741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3778374468450339220851827 5667561702675508831277741)
      ·
        refine ⟨2125335638503315811729153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5667561702675508831277741 2125335638503315811729153)
        ·
          refine ⟨1594001728877486858796865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2125335638503315811729153 1594001728877486858796865)
          ·
            refine ⟨1195501296658115144097649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1594001728877486858796865 1195501296658115144097649)
            ·
              refine ⟨896625972493586358073237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195501296658115144097649 896625972493586358073237)
              ·
                refine ⟨42029342460636860534683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 896625972493586358073237 42029342460636860534683)
                ·
                  rfl

theorem cell20_276250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_276250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276250 prefixEnd_276250 := by exact prefixLift 276250
  have htrace : WordTrace (prefixWord ++ tailWord_276250) baseStart_276250 baseEnd_276250 := by
    simpa [prefixWord, tailWord_276250, baseEnd_276250] using wordTrace_append hprefix tailTrace_276250
  have hstable : (prefixWord ++ tailWord_276250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276250).length < 2 ^ (prefixWord ++ tailWord_276250).sum := by decide
  have hdescent : baseEnd_276250 < baseStart_276250 := by decide
  rcases family_descends (prefixWord ++ tailWord_276250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276270 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_276270 : Nat := 118140960795 + 276270 * 2 ^ 59
def prefixEnd_276270 : Nat := 4983230072969 + 3 ^ 40 * 276270 * 2
def baseEnd_276270 : Nat := 126097155926879400937301

theorem tailTrace_276270 : CollatzResearch.WordTrace tailWord_276270 prefixEnd_276270 126097155926879400937301 := by
  unfold tailWord_276270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259549338641056000583283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6717596472752298669777509 1259549338641056000583283)
  ·
    refine ⟨1889324007961584000874925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1259549338641056000583283 1889324007961584000874925)
    ·
      refine ⟨708496502985594000328097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1889324007961584000874925 708496502985594000328097)
      ·
        refine ⟨531372377239195500246073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 708496502985594000328097 531372377239195500246073)
        ·
          refine ⟨398529282929396625184555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531372377239195500246073 398529282929396625184555)
          ·
            refine ⟨597793924394094937776833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398529282929396625184555 597793924394094937776833)
            ·
              refine ⟨448345443295571203332625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597793924394094937776833 448345443295571203332625)
              ·
                refine ⟨336259082471678402499469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448345443295571203332625 336259082471678402499469)
                ·
                  refine ⟨126097155926879400937301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336259082471678402499469 126097155926879400937301)
                  ·
                    rfl

theorem cell20_276270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_276270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276270 prefixEnd_276270 := by exact prefixLift 276270
  have htrace : WordTrace (prefixWord ++ tailWord_276270) baseStart_276270 baseEnd_276270 := by
    simpa [prefixWord, tailWord_276270, baseEnd_276270] using wordTrace_append hprefix tailTrace_276270
  have hstable : (prefixWord ++ tailWord_276270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276270).length < 2 ^ (prefixWord ++ tailWord_276270).sum := by decide
  have hdescent : baseEnd_276270 < baseStart_276270 := by decide
  rcases family_descends (prefixWord ++ tailWord_276270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276274 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_276274 : Nat := 118140960795 + 276274 * 2 ^ 59
def prefixEnd_276274 : Nat := 4983230072969 + 3 ^ 40 * 276274 * 2
def baseEnd_276274 : Nat := 126098981635873164803951

theorem tailTrace_276274 : CollatzResearch.WordTrace tailWord_276274 prefixEnd_276274 126098981635873164803951 := by
  unfold tailWord_276274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519135150278489171952969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6717693734075971125207917 2519135150278489171952969)
  ·
    refine ⟨1889351362708866878964727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2519135150278489171952969 1889351362708866878964727)
    ·
      refine ⟨2834027044063300318447091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1889351362708866878964727 2834027044063300318447091)
      ·
        refine ⟨4251040566094950477670637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2834027044063300318447091 4251040566094950477670637)
        ·
          refine ⟨1594140212285606429126489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4251040566094950477670637 1594140212285606429126489)
          ·
            refine ⟨1195605159214204821844867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1594140212285606429126489 1195605159214204821844867)
            ·
              refine ⟨1793407738821307232767301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195605159214204821844867 1793407738821307232767301)
              ·
                refine ⟨336263951028995106143869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1793407738821307232767301 336263951028995106143869)
                ·
                  refine ⟨126098981635873164803951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336263951028995106143869 126098981635873164803951)
                  ·
                    rfl

theorem cell20_276274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_276274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276274 prefixEnd_276274 := by exact prefixLift 276274
  have htrace : WordTrace (prefixWord ++ tailWord_276274) baseStart_276274 baseEnd_276274 := by
    simpa [prefixWord, tailWord_276274, baseEnd_276274] using wordTrace_append hprefix tailTrace_276274
  have hstable : (prefixWord ++ tailWord_276274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276274).length < 2 ^ (prefixWord ++ tailWord_276274).sum := by decide
  have hdescent : baseEnd_276274 < baseStart_276274 := by decide
  rcases family_descends (prefixWord ++ tailWord_276274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276277 : List Nat := [1, 3, 3, 1, 4, 1, 1, 4, 2]
def baseStart_276277 : Nat := 118140960795 + 276277 * 2 ^ 59
def prefixEnd_276277 : Nat := 4983230072969 + 3 ^ 40 * 276277 * 2
def baseEnd_276277 : Nat := 126100350917618487703939

theorem tailTrace_276277 : CollatzResearch.WordTrace tailWord_276277 prefixEnd_276277 126100350917618487703939 := by
  unfold tailWord_276277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10076650020103088200171085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6717766680068725466780723 10076650020103088200171085)
  ·
    refine ⟨3778743757538658075064157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10076650020103088200171085 3778743757538658075064157)
    ·
      refine ⟨1417028909076996778149059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3778743757538658075064157 1417028909076996778149059)
      ·
        refine ⟨2125543363615495167223589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417028909076996778149059 2125543363615495167223589)
        ·
          refine ⟨398539380677905343854423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2125543363615495167223589 398539380677905343854423)
          ·
            refine ⟨597809071016858015781635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398539380677905343854423 597809071016858015781635)
            ·
              refine ⟨896713606525287023672453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597809071016858015781635 896713606525287023672453)
              ·
                refine ⟨168133801223491316938585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 896713606525287023672453 168133801223491316938585)
                ·
                  refine ⟨126100350917618487703939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168133801223491316938585 126100350917618487703939)
                  ·
                    rfl

theorem cell20_276277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_276277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276277 prefixEnd_276277 := by exact prefixLift 276277
  have htrace : WordTrace (prefixWord ++ tailWord_276277) baseStart_276277 baseEnd_276277 := by
    simpa [prefixWord, tailWord_276277, baseEnd_276277] using wordTrace_append hprefix tailTrace_276277
  have hstable : (prefixWord ++ tailWord_276277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276277).length < 2 ^ (prefixWord ++ tailWord_276277).sum := by decide
  have hdescent : baseEnd_276277 < baseStart_276277 := by decide
  rcases family_descends (prefixWord ++ tailWord_276277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276305 : List Nat := [1, 2, 2, 1, 5, 2, 3, 4]
def baseStart_276305 : Nat := 118140960795 + 276305 * 2 ^ 59
def prefixEnd_276305 : Nat := 4983230072969 + 3 ^ 40 * 276305 * 2
def baseEnd_276305 : Nat := 42037710293524944923497

theorem tailTrace_276305 : CollatzResearch.WordTrace tailWord_276305 prefixEnd_276305 42037710293524944923497 := by
  unfold tailWord_276305
  simp only [CollatzResearch.WordTrace]
  refine ⟨10077671264001648982190369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6718447509334432654793579 10077671264001648982190369)
  ·
    refine ⟨7558253448001236736642777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10077671264001648982190369 7558253448001236736642777)
    ·
      refine ⟨5668690086000927552482083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7558253448001236736642777 5668690086000927552482083)
      ·
        refine ⟨8503035129001391328723125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5668690086000927552482083 8503035129001391328723125)
        ·
          refine ⟨797159543343880437067793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8503035129001391328723125 797159543343880437067793)
          ·
            refine ⟨597869657507910327800845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 797159543343880437067793 597869657507910327800845)
            ·
              refine ⟨224201121565466372925317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 597869657507910327800845 224201121565466372925317)
              ·
                refine ⟨42037710293524944923497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224201121565466372925317 42037710293524944923497)
                ·
                  rfl

theorem cell20_276305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 4].length) (baseStart_276305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276305 prefixEnd_276305 := by exact prefixLift 276305
  have htrace : WordTrace (prefixWord ++ tailWord_276305) baseStart_276305 baseEnd_276305 := by
    simpa [prefixWord, tailWord_276305, baseEnd_276305] using wordTrace_append hprefix tailTrace_276305
  have hstable : (prefixWord ++ tailWord_276305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276305).length < 2 ^ (prefixWord ++ tailWord_276305).sum := by decide
  have hdescent : baseEnd_276305 < baseStart_276305 := by decide
  rcases family_descends (prefixWord ++ tailWord_276305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276347 : List Nat := [1, 1, 1, 1, 1, 5, 1, 9]
def baseStart_276347 : Nat := 118140960795 + 276347 * 2 ^ 59
def prefixEnd_276347 : Nat := 4983230072969 + 3 ^ 40 * 276347 * 2
def baseEnd_276347 : Nat := 42044100275003118456773

theorem tailTrace_276347 : CollatzResearch.WordTrace tailWord_276347 prefixEnd_276347 42044100275003118456773 := by
  unfold tailWord_276347
  simp only [CollatzResearch.WordTrace]
  refine ⟨10079203129849490155219295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6719468753232993436812863 10079203129849490155219295)
  ·
    refine ⟨15118804694774235232828943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10079203129849490155219295 15118804694774235232828943)
    ·
      refine ⟨22678207042161352849243415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15118804694774235232828943 22678207042161352849243415)
      ·
        refine ⟨34017310563242029273865123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22678207042161352849243415 34017310563242029273865123)
        ·
          refine ⟨51025965844863043910797685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34017310563242029273865123 51025965844863043910797685)
          ·
            refine ⟨4783684297955910366637283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51025965844863043910797685 4783684297955910366637283)
            ·
              refine ⟨7175526446933865549955925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4783684297955910366637283 7175526446933865549955925)
              ·
                refine ⟨42044100275003118456773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7175526446933865549955925 42044100275003118456773)
                ·
                  rfl

theorem cell20_276347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_276347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276347 prefixEnd_276347 := by exact prefixLift 276347
  have htrace : WordTrace (prefixWord ++ tailWord_276347) baseStart_276347 baseEnd_276347 := by
    simpa [prefixWord, tailWord_276347, baseEnd_276347] using wordTrace_append hprefix tailTrace_276347
  have hstable : (prefixWord ++ tailWord_276347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276347).length < 2 ^ (prefixWord ++ tailWord_276347).sum := by decide
  have hdescent : baseEnd_276347 < baseStart_276347 := by decide
  rcases family_descends (prefixWord ++ tailWord_276347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276360 : List Nat := [2, 1, 3, 3, 3, 2, 2, 4]
def baseStart_276360 : Nat := 118140960795 + 276360 * 2 ^ 59
def prefixEnd_276360 : Nat := 4983230072969 + 3 ^ 40 * 276360 * 2
def baseEnd_276360 : Nat := 42046078126413029312311

theorem tailTrace_276360 : CollatzResearch.WordTrace tailWord_276360 prefixEnd_276360 42046078126413029312311 := by
  unfold tailWord_276360
  simp only [CollatzResearch.WordTrace]
  refine ⟨5039838639401196687721267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6719784852534928916961689 5039838639401196687721267)
  ·
    refine ⟨7559757959101795031581901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5039838639401196687721267 7559757959101795031581901)
    ·
      refine ⟨2834909234663173136843213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7559757959101795031581901 2834909234663173136843213)
      ·
        refine ⟨1063090962998689926316205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2834909234663173136843213 1063090962998689926316205)
        ·
          refine ⟨398659111124508722368577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1063090962998689926316205 398659111124508722368577)
          ·
            refine ⟨298994333343381541776433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398659111124508722368577 298994333343381541776433)
            ·
              refine ⟨224245750007536156332325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298994333343381541776433 224245750007536156332325)
              ·
                refine ⟨42046078126413029312311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224245750007536156332325 42046078126413029312311)
                ·
                  rfl

theorem cell20_276360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_276360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276360 prefixEnd_276360 := by exact prefixLift 276360
  have htrace : WordTrace (prefixWord ++ tailWord_276360) baseStart_276360 baseEnd_276360 := by
    simpa [prefixWord, tailWord_276360, baseEnd_276360] using wordTrace_append hprefix tailTrace_276360
  have hstable : (prefixWord ++ tailWord_276360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276360).length < 2 ^ (prefixWord ++ tailWord_276360).sum := by decide
  have hdescent : baseEnd_276360 < baseStart_276360 := by decide
  rcases family_descends (prefixWord ++ tailWord_276360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276370 : List Nat := [3, 2, 3, 2, 1, 3, 1, 3, 2]
def baseStart_276370 : Nat := 118140960795 + 276370 * 2 ^ 59
def prefixEnd_276370 : Nat := 4983230072969 + 3 ^ 40 * 276370 * 2
def baseEnd_276370 : Nat := 126142798651723497603559

theorem tailTrace_276370 : CollatzResearch.WordTrace tailWord_276370 prefixEnd_276370 126142798651723497603559 := by
  unfold tailWord_276370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2520010502191541270826641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6720028005844110055537709 2520010502191541270826641)
  ·
    refine ⟨1890007876643655953119981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2520010502191541270826641 1890007876643655953119981)
    ·
      refine ⟨708752953741370982419993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1890007876643655953119981 708752953741370982419993)
      ·
        refine ⟨531564715306028236814995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 708752953741370982419993 531564715306028236814995)
        ·
          refine ⟨797347072959042355222493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531564715306028236814995 797347072959042355222493)
          ·
            refine ⟨299005152359640883208435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 797347072959042355222493 299005152359640883208435)
            ·
              refine ⟨448507728539461324812653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299005152359640883208435 448507728539461324812653)
              ·
                refine ⟨168190398202297996804745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448507728539461324812653 168190398202297996804745)
                ·
                  refine ⟨126142798651723497603559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168190398202297996804745 126142798651723497603559)
                  ·
                    rfl

theorem cell20_276370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_276370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276370 prefixEnd_276370 := by exact prefixLift 276370
  have htrace : WordTrace (prefixWord ++ tailWord_276370) baseStart_276370 baseEnd_276370 := by
    simpa [prefixWord, tailWord_276370, baseEnd_276370] using wordTrace_append hprefix tailTrace_276370
  have hstable : (prefixWord ++ tailWord_276370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276370).length < 2 ^ (prefixWord ++ tailWord_276370).sum := by decide
  have hdescent : baseEnd_276370 < baseStart_276370 := by decide
  rcases family_descends (prefixWord ++ tailWord_276370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276405 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 3]
def baseStart_276405 : Nat := 118140960795 + 276405 * 2 ^ 59
def prefixEnd_276405 : Nat := 4983230072969 + 3 ^ 40 * 276405 * 2
def baseEnd_276405 : Nat := 126158773605418931436749

theorem tailTrace_276405 : CollatzResearch.WordTrace tailWord_276405 prefixEnd_276405 126158773605418931436749 := by
  unfold tailWord_276405
  simp only [CollatzResearch.WordTrace]
  refine ⟨10081318563639366060830669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6720879042426244040553779 10081318563639366060830669)
  ·
    refine ⟨3780494461364762272811501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10081318563639366060830669 3780494461364762272811501)
    ·
      refine ⟨1417685423011785852304313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3780494461364762272811501 1417685423011785852304313)
      ·
        refine ⟨1063264067258839389228235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1417685423011785852304313 1063264067258839389228235)
        ·
          refine ⟨1594896100888259083842353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063264067258839389228235 1594896100888259083842353)
          ·
            refine ⟨1196172075666194312881765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1594896100888259083842353 1196172075666194312881765)
            ·
              refine ⟨224282264187411433665331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1196172075666194312881765 224282264187411433665331)
              ·
                refine ⟨336423396281117150497997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224282264187411433665331 336423396281117150497997)
                ·
                  refine ⟨126158773605418931436749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336423396281117150497997 126158773605418931436749)
                  ·
                    rfl

theorem cell20_276405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_276405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276405 prefixEnd_276405 := by exact prefixLift 276405
  have htrace : WordTrace (prefixWord ++ tailWord_276405) baseStart_276405 baseEnd_276405 := by
    simpa [prefixWord, tailWord_276405, baseEnd_276405] using wordTrace_append hprefix tailTrace_276405
  have hstable : (prefixWord ++ tailWord_276405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276405).length < 2 ^ (prefixWord ++ tailWord_276405).sum := by decide
  have hdescent : baseEnd_276405 < baseStart_276405 := by decide
  rcases family_descends (prefixWord ++ tailWord_276405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276416 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_276416 : Nat := 118140960795 + 276416 * 2 ^ 59
def prefixEnd_276416 : Nat := 4983230072969 + 3 ^ 40 * 276416 * 2
def baseEnd_276416 : Nat := 126163794305151782070037

theorem tailTrace_276416 : CollatzResearch.WordTrace tailWord_276416 prefixEnd_276416 126163794305151782070037 := by
  unfold tailWord_276416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5040859883299757469740551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6721146511066343292987401 5040859883299757469740551)
  ·
    refine ⟨7561289824949636204610827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5040859883299757469740551 7561289824949636204610827)
    ·
      refine ⟨11341934737424454306916241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7561289824949636204610827 11341934737424454306916241)
      ·
        refine ⟨8506451053068340730187181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11341934737424454306916241 8506451053068340730187181)
        ·
          refine ⟨3189919144900627773820193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8506451053068340730187181 3189919144900627773820193)
          ·
            refine ⟨2392439358675470830365145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3189919144900627773820193 2392439358675470830365145)
            ·
              refine ⟨1794329519006603122773859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2392439358675470830365145 1794329519006603122773859)
              ·
                refine ⟨2691494278509904684160789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794329519006603122773859 2691494278509904684160789)
                ·
                  refine ⟨126163794305151782070037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2691494278509904684160789 126163794305151782070037)
                  ·
                    rfl

theorem cell20_276416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_276416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276416 prefixEnd_276416 := by exact prefixLift 276416
  have htrace : WordTrace (prefixWord ++ tailWord_276416) baseStart_276416 baseEnd_276416 := by
    simpa [prefixWord, tailWord_276416, baseEnd_276416] using wordTrace_append hprefix tailTrace_276416
  have hstable : (prefixWord ++ tailWord_276416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276416).length < 2 ^ (prefixWord ++ tailWord_276416).sum := by decide
  have hdescent : baseEnd_276416 < baseStart_276416 := by decide
  rcases family_descends (prefixWord ++ tailWord_276416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276484 : List Nat := [2, 3, 2, 4, 1, 1, 2, 3, 2]
def baseStart_276484 : Nat := 118140960795 + 276484 * 2 ^ 59
def prefixEnd_276484 : Nat := 4983230072969 + 3 ^ 40 * 276484 * 2
def baseEnd_276484 : Nat := 126194831358045767803093

theorem tailTrace_276484 : CollatzResearch.WordTrace tailWord_276484 prefixEnd_276484 126194831358045767803093 := by
  unfold tailWord_276484
  simp only [CollatzResearch.WordTrace]
  refine ⟨5042099965176581276478253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6722799953568775035304337 5042099965176581276478253)
  ·
    refine ⟨1890787486941217978679345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5042099965176581276478253 1890787486941217978679345)
    ·
      refine ⟨1418090615205913484009509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1890787486941217978679345 1418090615205913484009509)
      ·
        refine ⟨265891990351108778251783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1418090615205913484009509 265891990351108778251783)
        ·
          refine ⟨398837985526663167377675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265891990351108778251783 398837985526663167377675)
          ·
            refine ⟨598256978289994751066513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398837985526663167377675 598256978289994751066513)
            ·
              refine ⟨448692733717496063299885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598256978289994751066513 448692733717496063299885)
              ·
                refine ⟨168259775144061023737457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448692733717496063299885 168259775144061023737457)
                ·
                  refine ⟨126194831358045767803093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168259775144061023737457 126194831358045767803093)
                  ·
                    rfl

theorem cell20_276484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_276484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276484 prefixEnd_276484 := by exact prefixLift 276484
  have htrace : WordTrace (prefixWord ++ tailWord_276484) baseStart_276484 baseEnd_276484 := by
    simpa [prefixWord, tailWord_276484, baseEnd_276484] using wordTrace_append hprefix tailTrace_276484
  have hstable : (prefixWord ++ tailWord_276484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276484).length < 2 ^ (prefixWord ++ tailWord_276484).sum := by decide
  have hdescent : baseEnd_276484 < baseStart_276484 := by decide
  rcases family_descends (prefixWord ++ tailWord_276484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276488 : List Nat := [2, 1, 3, 2, 1, 2, 4, 3, 2]
def baseStart_276488 : Nat := 118140960795 + 276488 * 2 ^ 59
def prefixEnd_276488 : Nat := 4983230072969 + 3 ^ 40 * 276488 * 2
def baseEnd_276488 : Nat := 126196657067039531669743

theorem tailTrace_276488 : CollatzResearch.WordTrace tailWord_276488 prefixEnd_276488 126196657067039531669743 := by
  unfold tailWord_276488
  simp only [CollatzResearch.WordTrace]
  refine ⟨5042172911169335618051059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6722897214892447490734745 5042172911169335618051059)
  ·
    refine ⟨7563259366754003427076589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5042172911169335618051059 7563259366754003427076589)
    ·
      refine ⟨2836222262532751285153721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7563259366754003427076589 2836222262532751285153721)
      ·
        refine ⟨2127166696899563463865291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2836222262532751285153721 2127166696899563463865291)
        ·
          refine ⟨3190750045349345195797937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127166696899563463865291 3190750045349345195797937)
          ·
            refine ⟨2393062534012008896848453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3190750045349345195797937 2393062534012008896848453)
            ·
              refine ⟨448699225127251668159085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2393062534012008896848453 448699225127251668159085)
              ·
                refine ⟨168262209422719375559657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448699225127251668159085 168262209422719375559657)
                ·
                  refine ⟨126196657067039531669743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168262209422719375559657 126196657067039531669743)
                  ·
                    rfl

theorem cell20_276488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_276488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276488 prefixEnd_276488 := by exact prefixLift 276488
  have htrace : WordTrace (prefixWord ++ tailWord_276488) baseStart_276488 baseEnd_276488 := by
    simpa [prefixWord, tailWord_276488, baseEnd_276488] using wordTrace_append hprefix tailTrace_276488
  have hstable : (prefixWord ++ tailWord_276488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276488).length < 2 ^ (prefixWord ++ tailWord_276488).sum := by decide
  have hdescent : baseEnd_276488 < baseStart_276488 := by decide
  rcases family_descends (prefixWord ++ tailWord_276488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276492 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_276492 : Nat := 118140960795 + 276492 * 2 ^ 59
def prefixEnd_276492 : Nat := 4983230072969 + 3 ^ 40 * 276492 * 2
def baseEnd_276492 : Nat := 126198482776033295536393

theorem tailTrace_276492 : CollatzResearch.WordTrace tailWord_276492 prefixEnd_276492 126198482776033295536393 := by
  unfold tailWord_276492
  simp only [CollatzResearch.WordTrace]
  refine ⟨5042245857162089959623865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6722994476216119946165153 5042245857162089959623865)
  ·
    refine ⟨3781684392871567469717899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5042245857162089959623865 3781684392871567469717899)
    ·
      refine ⟨5672526589307351204576849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3781684392871567469717899 5672526589307351204576849)
      ·
        refine ⟨4254394941980513403432637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5672526589307351204576849 4254394941980513403432637)
        ·
          refine ⟨1595398103242692526287239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4254394941980513403432637 1595398103242692526287239)
          ·
            refine ⟨2393097154864038789430859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595398103242692526287239 2393097154864038789430859)
            ·
              refine ⟨3589645732296058184146289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393097154864038789430859 3589645732296058184146289)
              ·
                refine ⟨2692234299222043638109717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3589645732296058184146289 2692234299222043638109717)
                ·
                  refine ⟨126198482776033295536393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2692234299222043638109717 126198482776033295536393)
                  ·
                    rfl

theorem cell20_276492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_276492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276492 prefixEnd_276492 := by exact prefixLift 276492
  have htrace : WordTrace (prefixWord ++ tailWord_276492) baseStart_276492 baseEnd_276492 := by
    simpa [prefixWord, tailWord_276492, baseEnd_276492] using wordTrace_append hprefix tailTrace_276492
  have hstable : (prefixWord ++ tailWord_276492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276492).length < 2 ^ (prefixWord ++ tailWord_276492).sum := by decide
  have hdescent : baseEnd_276492 < baseStart_276492 := by decide
  rcases family_descends (prefixWord ++ tailWord_276492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276509 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_276509 : Nat := 118140960795 + 276509 * 2 ^ 59
def prefixEnd_276509 : Nat := 4983230072969 + 3 ^ 40 * 276509 * 2
def baseEnd_276509 : Nat := 126206242039256791969657

theorem tailTrace_276509 : CollatzResearch.WordTrace tailWord_276509 prefixEnd_276509 126206242039256791969657 := by
  unfold tailWord_276509
  simp only [CollatzResearch.WordTrace]
  refine ⟨10085111755262591822616581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6723407836841727881744387 10085111755262591822616581)
  ·
    refine ⟨1890958454111735966740609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10085111755262591822616581 1890958454111735966740609)
    ·
      refine ⟨1418218840583801975055457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1890958454111735966740609 1418218840583801975055457)
      ·
        refine ⟨1063664130437851481291593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1418218840583801975055457 1063664130437851481291593)
        ·
          refine ⟨797748097828388610968695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1063664130437851481291593 797748097828388610968695)
          ·
            refine ⟨1196622146742582916453043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797748097828388610968695 1196622146742582916453043)
            ·
              refine ⟨1794933220113874374679565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196622146742582916453043 1794933220113874374679565)
              ·
                refine ⟨673099957542702890504837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1794933220113874374679565 673099957542702890504837)
                ·
                  refine ⟨126206242039256791969657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 673099957542702890504837 126206242039256791969657)
                  ·
                    rfl

theorem cell20_276509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_276509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276509 prefixEnd_276509 := by exact prefixLift 276509
  have htrace : WordTrace (prefixWord ++ tailWord_276509) baseStart_276509 baseEnd_276509 := by
    simpa [prefixWord, tailWord_276509, baseEnd_276509] using wordTrace_append hprefix tailTrace_276509
  have hstable : (prefixWord ++ tailWord_276509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276509).length < 2 ^ (prefixWord ++ tailWord_276509).sum := by decide
  have hdescent : baseEnd_276509 < baseStart_276509 := by decide
  rcases family_descends (prefixWord ++ tailWord_276509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276547 : List Nat := [1, 1, 1, 3, 1, 2, 2, 7, 2]
def baseStart_276547 : Nat := 118140960795 + 276547 * 2 ^ 59
def prefixEnd_276547 : Nat := 4983230072969 + 3 ^ 40 * 276547 * 2
def baseEnd_276547 : Nat := 126223586274697548702835

theorem tailTrace_276547 : CollatzResearch.WordTrace tailWord_276547 prefixEnd_276547 126223586274697548702835 := by
  unfold tailWord_276547
  simp only [CollatzResearch.WordTrace]
  refine ⟨10086497729124924312499895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6724331819416616208333263 10086497729124924312499895)
  ·
    refine ⟨15129746593687386468749843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10086497729124924312499895 15129746593687386468749843)
    ·
      refine ⟨22694619890531079703124765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15129746593687386468749843 22694619890531079703124765)
      ·
        refine ⟨8510482458949154888671787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22694619890531079703124765 8510482458949154888671787)
        ·
          refine ⟨12765723688423732333007681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8510482458949154888671787 12765723688423732333007681)
          ·
            refine ⟨9574292766317799249755761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12765723688423732333007681 9574292766317799249755761)
            ·
              refine ⟨7180719574738349437316821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9574292766317799249755761 7180719574738349437316821)
              ·
                refine ⟨168298115032930064937113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7180719574738349437316821 168298115032930064937113)
                ·
                  refine ⟨126223586274697548702835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168298115032930064937113 126223586274697548702835)
                  ·
                    rfl

theorem cell20_276547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 2].length) (baseStart_276547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276547 prefixEnd_276547 := by exact prefixLift 276547
  have htrace : WordTrace (prefixWord ++ tailWord_276547) baseStart_276547 baseEnd_276547 := by
    simpa [prefixWord, tailWord_276547, baseEnd_276547] using wordTrace_append hprefix tailTrace_276547
  have hstable : (prefixWord ++ tailWord_276547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276547).length < 2 ^ (prefixWord ++ tailWord_276547).sum := by decide
  have hdescent : baseEnd_276547 < baseStart_276547 := by decide
  rcases family_descends (prefixWord ++ tailWord_276547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276561 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 3]
def baseStart_276561 : Nat := 118140960795 + 276561 * 2 ^ 59
def prefixEnd_276561 : Nat := 4983230072969 + 3 ^ 40 * 276561 * 2
def baseEnd_276561 : Nat := 126229976256175722236111

theorem tailTrace_276561 : CollatzResearch.WordTrace tailWord_276561 prefixEnd_276561 126229976256175722236111 := by
  unfold tailWord_276561
  simp only [CollatzResearch.WordTrace]
  refine ⟨10087008351074204703509537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6724672234049469802339691 10087008351074204703509537)
  ·
    refine ⟨7565256263305653527632153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10087008351074204703509537 7565256263305653527632153)
    ·
      refine ⟨5673942197479240145724115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7565256263305653527632153 5673942197479240145724115)
      ·
        refine ⟨8510913296218860218586173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5673942197479240145724115 8510913296218860218586173)
        ·
          refine ⟨3191592486082072581969815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8510913296218860218586173 3191592486082072581969815)
          ·
            refine ⟨4787388729123108872954723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191592486082072581969815 4787388729123108872954723)
            ·
              refine ⟨7181083093684663309432085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4787388729123108872954723 7181083093684663309432085)
              ·
                refine ⟨336613270016468592629629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7181083093684663309432085 336613270016468592629629)
                ·
                  refine ⟨126229976256175722236111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336613270016468592629629 126229976256175722236111)
                  ·
                    rfl

theorem cell20_276561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_276561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276561 prefixEnd_276561 := by exact prefixLift 276561
  have htrace : WordTrace (prefixWord ++ tailWord_276561) baseStart_276561 baseEnd_276561 := by
    simpa [prefixWord, tailWord_276561, baseEnd_276561] using wordTrace_append hprefix tailTrace_276561
  have hstable : (prefixWord ++ tailWord_276561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276561).length < 2 ^ (prefixWord ++ tailWord_276561).sum := by decide
  have hdescent : baseEnd_276561 < baseStart_276561 := by decide
  rcases family_descends (prefixWord ++ tailWord_276561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276613 : List Nat := [1, 3, 1, 1, 5, 9]
def baseStart_276613 : Nat := 118140960795 + 276613 * 2 ^ 59
def prefixEnd_276613 : Nat := 4983230072969 + 3 ^ 40 * 276613 * 2
def baseEnd_276613 : Nat := 4676063350855357500095

theorem tailTrace_276613 : CollatzResearch.WordTrace tailWord_276613 prefixEnd_276613 4676063350855357500095 := by
  unfold tailWord_276613
  simp only [CollatzResearch.WordTrace]
  refine ⟨10088904946885817584402493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6725936631257211722934995 10088904946885817584402493)
  ·
    refine ⟨3783339355082181594150935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10088904946885817584402493 3783339355082181594150935)
    ·
      refine ⟨5675009032623272391226403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3783339355082181594150935 5675009032623272391226403)
      ·
        refine ⟨8512513548934908586839605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5675009032623272391226403 8512513548934908586839605)
        ·
          refine ⟨798048145212647680016213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8512513548934908586839605 798048145212647680016213)
          ·
            refine ⟨4676063350855357500095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 798048145212647680016213 4676063350855357500095)
            ·
              rfl

theorem cell20_276613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 9].length) (baseStart_276613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276613 prefixEnd_276613 := by exact prefixLift 276613
  have htrace : WordTrace (prefixWord ++ tailWord_276613) baseStart_276613 baseEnd_276613 := by
    simpa [prefixWord, tailWord_276613, baseEnd_276613] using wordTrace_append hprefix tailTrace_276613
  have hstable : (prefixWord ++ tailWord_276613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276613).length < 2 ^ (prefixWord ++ tailWord_276613).sum := by decide
  have hdescent : baseEnd_276613 < baseStart_276613 := by decide
  rcases family_descends (prefixWord ++ tailWord_276613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276616 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 3]
def baseStart_276616 : Nat := 118140960795 + 276616 * 2 ^ 59
def prefixEnd_276616 : Nat := 4983230072969 + 3 ^ 40 * 276616 * 2
def baseEnd_276616 : Nat := 126255079754839975402553

theorem tailTrace_276616 : CollatzResearch.WordTrace tailWord_276616 prefixEnd_276616 126255079754839975402553 := by
  unfold tailWord_276616
  simp only [CollatzResearch.WordTrace]
  refine ⟨5044507182937474548380851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6726009577249966064507801 5044507182937474548380851)
  ·
    refine ⟨7566760774406211822571277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5044507182937474548380851 7566760774406211822571277)
    ·
      refine ⟨2837535290402329433464229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7566760774406211822571277 2837535290402329433464229)
      ·
        refine ⟨532037866950436768774543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2837535290402329433464229 532037866950436768774543)
        ·
          refine ⟨798056800425655153161815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532037866950436768774543 798056800425655153161815)
          ·
            refine ⟨1197085200638482729742723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798056800425655153161815 1197085200638482729742723)
            ·
              refine ⟨1795627800957724094614085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197085200638482729742723 1795627800957724094614085)
              ·
                refine ⟨336680212679573267740141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1795627800957724094614085 336680212679573267740141)
                ·
                  refine ⟨126255079754839975402553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336680212679573267740141 126255079754839975402553)
                  ·
                    rfl

theorem cell20_276616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_276616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276616 prefixEnd_276616 := by exact prefixLift 276616
  have htrace : WordTrace (prefixWord ++ tailWord_276616) baseStart_276616 baseEnd_276616 := by
    simpa [prefixWord, tailWord_276616, baseEnd_276616] using wordTrace_append hprefix tailTrace_276616
  have hstable : (prefixWord ++ tailWord_276616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276616).length < 2 ^ (prefixWord ++ tailWord_276616).sum := by decide
  have hdescent : baseEnd_276616 < baseStart_276616 := by decide
  rcases family_descends (prefixWord ++ tailWord_276616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276657 : List Nat := [1, 2, 2, 5, 2, 1, 2, 3, 2]
def baseStart_276657 : Nat := 118140960795 + 276657 * 2 ^ 59
def prefixEnd_276657 : Nat := 4983230072969 + 3 ^ 40 * 276657 * 2
def baseEnd_276657 : Nat := 126273793272026055035719

theorem tailTrace_276657 : CollatzResearch.WordTrace tailWord_276657 prefixEnd_276657 126273793272026055035719 := by
  unfold tailWord_276657
  simp only [CollatzResearch.WordTrace]
  refine ⟨10090509758726413099004225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6727006505817608732669483 10090509758726413099004225)
  ·
    refine ⟨7567882319044809824253169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10090509758726413099004225 7567882319044809824253169)
    ·
      refine ⟨5675911739283607368189877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7567882319044809824253169 5675911739283607368189877)
      ·
        refine ⟨532116725557838190767801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5675911739283607368189877 532116725557838190767801)
        ·
          refine ⟨399087544168378643075851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 532116725557838190767801 399087544168378643075851)
          ·
            refine ⟨598631316252567964613777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399087544168378643075851 598631316252567964613777)
            ·
              refine ⟨448973487189425973460333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598631316252567964613777 448973487189425973460333)
              ·
                refine ⟨168365057696034740047625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448973487189425973460333 168365057696034740047625)
                ·
                  refine ⟨126273793272026055035719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168365057696034740047625 126273793272026055035719)
                  ·
                    rfl

theorem cell20_276657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_276657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276657 prefixEnd_276657 := by exact prefixLift 276657
  have htrace : WordTrace (prefixWord ++ tailWord_276657) baseStart_276657 baseEnd_276657 := by
    simpa [prefixWord, tailWord_276657, baseEnd_276657] using wordTrace_append hprefix tailTrace_276657
  have hstable : (prefixWord ++ tailWord_276657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276657).length < 2 ^ (prefixWord ++ tailWord_276657).sum := by decide
  have hdescent : baseEnd_276657 < baseStart_276657 := by decide
  rcases family_descends (prefixWord ++ tailWord_276657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276668 : List Nat := [2, 2, 2, 3, 3, 1, 7]
def baseStart_276668 : Nat := 118140960795 + 276668 * 2 ^ 59
def prefixEnd_276668 : Nat := 4983230072969 + 3 ^ 40 * 276668 * 2
def baseEnd_276668 : Nat := 14030979330195433963223

theorem tailTrace_276668 : CollatzResearch.WordTrace tailWord_276668 prefixEnd_276668 14030979330195433963223 := by
  unfold tailWord_276668
  simp only [CollatzResearch.WordTrace]
  refine ⟨5045455480843280988827329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6727273974457707985103105 5045455480843280988827329)
  ·
    refine ⟨3784091610632460741620497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5045455480843280988827329 3784091610632460741620497)
    ·
      refine ⟨2838068707974345556215373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3784091610632460741620497 2838068707974345556215373)
      ·
        refine ⟨1064275765490379583580765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2838068707974345556215373 1064275765490379583580765)
        ·
          refine ⟨399103412058892343842787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1064275765490379583580765 399103412058892343842787)
          ·
            refine ⟨598655118088338515764181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399103412058892343842787 598655118088338515764181)
            ·
              refine ⟨14030979330195433963223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 598655118088338515764181 14030979330195433963223)
              ·
                rfl

theorem cell20_276668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 7].length) (baseStart_276668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276668 prefixEnd_276668 := by exact prefixLift 276668
  have htrace : WordTrace (prefixWord ++ tailWord_276668) baseStart_276668 baseEnd_276668 := by
    simpa [prefixWord, tailWord_276668, baseEnd_276668] using wordTrace_append hprefix tailTrace_276668
  have hstable : (prefixWord ++ tailWord_276668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276668).length < 2 ^ (prefixWord ++ tailWord_276668).sum := by decide
  have hdescent : baseEnd_276668 < baseStart_276668 := by decide
  rcases family_descends (prefixWord ++ tailWord_276668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276674 : List Nat := [3, 5, 1, 1, 1, 1, 2, 4, 2]
def baseStart_276674 : Nat := 118140960795 + 276674 * 2 ^ 59
def prefixEnd_276674 : Nat := 4983230072969 + 3 ^ 40 * 276674 * 2
def baseEnd_276674 : Nat := 126281552535249551468983

theorem tailTrace_276674 : CollatzResearch.WordTrace tailWord_276674 prefixEnd_276674 126281552535249551468983 := by
  unfold tailWord_276674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2522782449916206250593269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6727419866443216668248717 2522782449916206250593269)
  ·
    refine ⟨236510854679644335993119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2522782449916206250593269 236510854679644335993119)
    ·
      refine ⟨354766282019466503989679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236510854679644335993119 354766282019466503989679)
      ·
        refine ⟨532149423029199755984519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354766282019466503989679 532149423029199755984519)
        ·
          refine ⟨798224134543799633976779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532149423029199755984519 798224134543799633976779)
          ·
            refine ⟨1197336201815699450965169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798224134543799633976779 1197336201815699450965169)
            ·
              refine ⟨898002151361774588223877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1197336201815699450965169 898002151361774588223877)
              ·
                refine ⟨168375403380332735291977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 898002151361774588223877 168375403380332735291977)
                ·
                  refine ⟨126281552535249551468983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168375403380332735291977 126281552535249551468983)
                  ·
                    rfl

theorem cell20_276674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_276674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276674 prefixEnd_276674 := by exact prefixLift 276674
  have htrace : WordTrace (prefixWord ++ tailWord_276674) baseStart_276674 baseEnd_276674 := by
    simpa [prefixWord, tailWord_276674, baseEnd_276674] using wordTrace_append hprefix tailTrace_276674
  have hstable : (prefixWord ++ tailWord_276674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276674).length < 2 ^ (prefixWord ++ tailWord_276674).sum := by decide
  have hdescent : baseEnd_276674 < baseStart_276674 := by decide
  rcases family_descends (prefixWord ++ tailWord_276674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276743 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 3]
def baseStart_276743 : Nat := 118140960795 + 276743 * 2 ^ 59
def prefixEnd_276743 : Nat := 4983230072969 + 3 ^ 40 * 276743 * 2
def baseEnd_276743 : Nat := 126313046015391978168701

theorem tailTrace_276743 : CollatzResearch.WordTrace tailWord_276743 prefixEnd_276743 126313046015391978168701 := by
  unfold tailWord_276743
  simp only [CollatzResearch.WordTrace]
  refine ⟨10093646436414849786634883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6729097624276566524423255 10093646436414849786634883)
  ·
    refine ⟨15140469654622274679952325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10093646436414849786634883 15140469654622274679952325)
    ·
      refine ⟨2838838060241676502491061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15140469654622274679952325 2838838060241676502491061)
      ·
        refine ⟨266141068147657172108537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2838838060241676502491061 266141068147657172108537)
        ·
          refine ⟨199605801110742879081403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266141068147657172108537 199605801110742879081403)
          ·
            refine ⟨299408701666114318622105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199605801110742879081403 299408701666114318622105)
            ·
              refine ⟨224556526249585738966579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299408701666114318622105 224556526249585738966579)
              ·
                refine ⟨336834789374378608449869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224556526249585738966579 336834789374378608449869)
                ·
                  refine ⟨126313046015391978168701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336834789374378608449869 126313046015391978168701)
                  ·
                    rfl

theorem cell20_276743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 3].length) (baseStart_276743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276743 prefixEnd_276743 := by exact prefixLift 276743
  have htrace : WordTrace (prefixWord ++ tailWord_276743) baseStart_276743 baseEnd_276743 := by
    simpa [prefixWord, tailWord_276743, baseEnd_276743] using wordTrace_append hprefix tailTrace_276743
  have hstable : (prefixWord ++ tailWord_276743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276743).length < 2 ^ (prefixWord ++ tailWord_276743).sum := by decide
  have hdescent : baseEnd_276743 < baseStart_276743 := by decide
  rcases family_descends (prefixWord ++ tailWord_276743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276744 : List Nat := [2, 1, 3, 2, 3, 2, 2, 5]
def baseStart_276744 : Nat := 118140960795 + 276744 * 2 ^ 59
def prefixEnd_276744 : Nat := 4983230072969 + 3 ^ 40 * 276744 * 2
def baseEnd_276744 : Nat := 42104500814213473045121

theorem tailTrace_276744 : CollatzResearch.WordTrace tailWord_276744 prefixEnd_276744 42104500814213473045121 := by
  unfold tailWord_276744
  simp only [CollatzResearch.WordTrace]
  refine ⟨5046841454705613478710643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6729121939607484638280857 5046841454705613478710643)
  ·
    refine ⟨7570262182058420218065965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5046841454705613478710643 7570262182058420218065965)
    ·
      refine ⟨2838848318271907581774737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7570262182058420218065965 2838848318271907581774737)
      ·
        refine ⟨2129136238703930686331053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2838848318271907581774737 2129136238703930686331053)
        ·
          refine ⟨798426089513974007374145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2129136238703930686331053 798426089513974007374145)
          ·
            refine ⟨598819567135480505530609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 798426089513974007374145 598819567135480505530609)
            ·
              refine ⟨449114675351610379147957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598819567135480505530609 449114675351610379147957)
              ·
                refine ⟨42104500814213473045121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 449114675351610379147957 42104500814213473045121)
                ·
                  rfl

theorem cell20_276744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_276744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276744 prefixEnd_276744 := by exact prefixLift 276744
  have htrace : WordTrace (prefixWord ++ tailWord_276744) baseStart_276744 baseEnd_276744 := by
    simpa [prefixWord, tailWord_276744, baseEnd_276744] using wordTrace_append hprefix tailTrace_276744
  have hstable : (prefixWord ++ tailWord_276744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276744).length < 2 ^ (prefixWord ++ tailWord_276744).sum := by decide
  have hdescent : baseEnd_276744 < baseStart_276744 := by decide
  rcases family_descends (prefixWord ++ tailWord_276744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276782 : List Nat := [4, 1, 3, 3, 9]
def baseStart_276782 : Nat := 118140960795 + 276782 * 2 ^ 59
def prefixEnd_276782 : Nat := 4983230072969 + 3 ^ 40 * 276782 * 2
def baseEnd_276782 : Nat := 1559640082445446615661

theorem tailTrace_276782 : CollatzResearch.WordTrace tailWord_276782 prefixEnd_276782 1559640082445446615661 := by
  unfold tailWord_276782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1261883610409194930913075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6730045922182372964869733 1261883610409194930913075)
  ·
    refine ⟨1892825415613792396369613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1261883610409194930913075 1892825415613792396369613)
    ·
      refine ⟨709809530855172148638605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1892825415613792396369613 709809530855172148638605)
      ·
        refine ⟨266178574070689555739477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 709809530855172148638605 266178574070689555739477)
        ·
          refine ⟨1559640082445446615661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 266178574070689555739477 1559640082445446615661)
          ·
            rfl

theorem cell20_276782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 9].length) (baseStart_276782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276782 prefixEnd_276782 := by exact prefixLift 276782
  have htrace : WordTrace (prefixWord ++ tailWord_276782) baseStart_276782 baseEnd_276782 := by
    simpa [prefixWord, tailWord_276782, baseEnd_276782] using wordTrace_append hprefix tailTrace_276782
  have hstable : (prefixWord ++ tailWord_276782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276782).length < 2 ^ (prefixWord ++ tailWord_276782).sum := by decide
  have hdescent : baseEnd_276782 < baseStart_276782 := by decide
  rcases family_descends (prefixWord ++ tailWord_276782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276788 : List Nat := [2, 5, 1, 1, 1, 4, 2, 2, 2]
def baseStart_276788 : Nat := 118140960795 + 276788 * 2 ^ 59
def prefixEnd_276788 : Nat := 4983230072969 + 3 ^ 40 * 276788 * 2
def baseEnd_276788 : Nat := 126333585241571821668517

theorem tailTrace_276788 : CollatzResearch.WordTrace tailWord_276788 prefixEnd_276788 126333585241571821668517 := by
  unfold tailWord_276788
  simp only [CollatzResearch.WordTrace]
  refine ⟨5047643860625911236011509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6730191814167881648015345 5047643860625911236011509)
  ·
    refine ⟨473216611933679178376079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5047643860625911236011509 473216611933679178376079)
    ·
      refine ⟨709824917900518767564119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 473216611933679178376079 709824917900518767564119)
      ·
        refine ⟨1064737376850778151346179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709824917900518767564119 1064737376850778151346179)
        ·
          refine ⟨1597106065276167227019269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064737376850778151346179 1597106065276167227019269)
          ·
            refine ⟨299457387239281355066113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1597106065276167227019269 299457387239281355066113)
            ·
              refine ⟨224593040429461016299585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299457387239281355066113 224593040429461016299585)
              ·
                refine ⟨168444780322095762224689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224593040429461016299585 168444780322095762224689)
                ·
                  refine ⟨126333585241571821668517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168444780322095762224689 126333585241571821668517)
                  ·
                    rfl

theorem cell20_276788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_276788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276788 prefixEnd_276788 := by exact prefixLift 276788
  have htrace : WordTrace (prefixWord ++ tailWord_276788) baseStart_276788 baseEnd_276788 := by
    simpa [prefixWord, tailWord_276788, baseEnd_276788] using wordTrace_append hprefix tailTrace_276788
  have hstable : (prefixWord ++ tailWord_276788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276788).length < 2 ^ (prefixWord ++ tailWord_276788).sum := by decide
  have hdescent : baseEnd_276788 < baseStart_276788 := by decide
  rcases family_descends (prefixWord ++ tailWord_276788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276792 : List Nat := [2, 1, 2, 1, 3, 1, 6, 2, 2]
def baseStart_276792 : Nat := 118140960795 + 276792 * 2 ^ 59
def prefixEnd_276792 : Nat := 4983230072969 + 3 ^ 40 * 276792 * 2
def baseEnd_276792 : Nat := 126335410950565585535167

theorem tailTrace_276792 : CollatzResearch.WordTrace tailWord_276792 prefixEnd_276792 126335410950565585535167 := by
  unfold tailWord_276792
  simp only [CollatzResearch.WordTrace]
  refine ⟨5047716806618665577584315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6730289075491554103445753 5047716806618665577584315)
  ·
    refine ⟨7571575209927998366376473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5047716806618665577584315 7571575209927998366376473)
    ·
      refine ⟨5678681407445998774782355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7571575209927998366376473 5678681407445998774782355)
      ·
        refine ⟨8518022111168998162173533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5678681407445998774782355 8518022111168998162173533)
        ·
          refine ⟨3194258291688374310815075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8518022111168998162173533 3194258291688374310815075)
          ·
            refine ⟨4791387437532561466222613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194258291688374310815075 4791387437532561466222613)
            ·
              refine ⟨224596286134338818729185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4791387437532561466222613 224596286134338818729185)
              ·
                refine ⟨168447214600754114046889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224596286134338818729185 168447214600754114046889)
                ·
                  refine ⟨126335410950565585535167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168447214600754114046889 126335410950565585535167)
                  ·
                    rfl

theorem cell20_276792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_276792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276792 prefixEnd_276792 := by exact prefixLift 276792
  have htrace : WordTrace (prefixWord ++ tailWord_276792) baseStart_276792 baseEnd_276792 := by
    simpa [prefixWord, tailWord_276792, baseEnd_276792] using wordTrace_append hprefix tailTrace_276792
  have hstable : (prefixWord ++ tailWord_276792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276792).length < 2 ^ (prefixWord ++ tailWord_276792).sum := by decide
  have hdescent : baseEnd_276792 < baseStart_276792 := by decide
  rcases family_descends (prefixWord ++ tailWord_276792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276796 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_276796 : Nat := 118140960795 + 276796 * 2 ^ 59
def prefixEnd_276796 : Nat := 4983230072969 + 3 ^ 40 * 276796 * 2
def baseEnd_276796 : Nat := 126337236659559349401817

theorem tailTrace_276796 : CollatzResearch.WordTrace tailWord_276796 prefixEnd_276796 126337236659559349401817 := by
  unfold tailWord_276796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5047789752611419919157121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6730386336815226558876161 5047789752611419919157121)
  ·
    refine ⟨3785842314458564939367841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5047789752611419919157121 3785842314458564939367841)
    ·
      refine ⟨2839381735843923704525881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3785842314458564939367841 2839381735843923704525881)
      ·
        refine ⟨2129536301882942778394411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2839381735843923704525881 2129536301882942778394411)
        ·
          refine ⟨3194304452824414167591617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2129536301882942778394411 3194304452824414167591617)
          ·
            refine ⟨2395728339618310625693713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3194304452824414167591617 2395728339618310625693713)
            ·
              refine ⟨1796796254713732969270285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2395728339618310625693713 1796796254713732969270285)
              ·
                refine ⟨673798595517649863476357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1796796254713732969270285 673798595517649863476357)
                ·
                  refine ⟨126337236659559349401817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 673798595517649863476357 126337236659559349401817)
                  ·
                    rfl

theorem cell20_276796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_276796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276796 prefixEnd_276796 := by exact prefixLift 276796
  have htrace : WordTrace (prefixWord ++ tailWord_276796) baseStart_276796 baseEnd_276796 := by
    simpa [prefixWord, tailWord_276796, baseEnd_276796] using wordTrace_append hprefix tailTrace_276796
  have hstable : (prefixWord ++ tailWord_276796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276796).length < 2 ^ (prefixWord ++ tailWord_276796).sum := by decide
  have hdescent : baseEnd_276796 < baseStart_276796 := by decide
  rcases family_descends (prefixWord ++ tailWord_276796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276803 : List Nat := [1, 1, 1, 3, 1, 3, 5, 5]
def baseStart_276803 : Nat := 118140960795 + 276803 * 2 ^ 59
def prefixEnd_276803 : Nat := 4983230072969 + 3 ^ 40 * 276803 * 2
def baseEnd_276803 : Nat := 42113477216766145389485

theorem tailTrace_276803 : CollatzResearch.WordTrace tailWord_276803 prefixEnd_276803 42113477216766145389485 := by
  unfold tailWord_276803
  simp only [CollatzResearch.WordTrace]
  refine ⟨10095834816197480033819063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6730556544131653355879375 10095834816197480033819063)
  ·
    refine ⟨15143752224296220050728595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10095834816197480033819063 15143752224296220050728595)
    ·
      refine ⟨22715628336444330076092893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15143752224296220050728595 22715628336444330076092893)
      ·
        refine ⟨8518360626166623778534835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22715628336444330076092893 8518360626166623778534835)
        ·
          refine ⟨12777540939249935667802253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8518360626166623778534835 12777540939249935667802253)
          ·
            refine ⟨4791577852218725875425845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12777540939249935667802253 4791577852218725875425845)
            ·
              refine ⟨449210423645505550821173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4791577852218725875425845 449210423645505550821173)
              ·
                refine ⟨42113477216766145389485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 449210423645505550821173 42113477216766145389485)
                ·
                  rfl

theorem cell20_276803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_276803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276803 prefixEnd_276803 := by exact prefixLift 276803
  have htrace : WordTrace (prefixWord ++ tailWord_276803) baseStart_276803 baseEnd_276803 := by
    simpa [prefixWord, tailWord_276803, baseEnd_276803] using wordTrace_append hprefix tailTrace_276803
  have hstable : (prefixWord ++ tailWord_276803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276803).length < 2 ^ (prefixWord ++ tailWord_276803).sum := by decide
  have hdescent : baseEnd_276803 < baseStart_276803 := by decide
  rcases family_descends (prefixWord ++ tailWord_276803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276810 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_276810 : Nat := 118140960795 + 276810 * 2 ^ 59
def prefixEnd_276810 : Nat := 4983230072969 + 3 ^ 40 * 276810 * 2
def baseEnd_276810 : Nat := 126343626641037522935093

theorem tailTrace_276810 : CollatzResearch.WordTrace tailWord_276810 prefixEnd_276810 126343626641037522935093 := by
  unfold tailWord_276810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2524022531793030057330971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6730726751448080152882589 2524022531793030057330971)
  ·
    refine ⟨3786033797689545085996457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2524022531793030057330971 3786033797689545085996457)
    ·
      refine ⟨2839525348267158814497343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3786033797689545085996457 2839525348267158814497343)
      ·
        refine ⟨4259288022400738221746015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2839525348267158814497343 4259288022400738221746015)
        ·
          refine ⟨6388932033601107332619023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4259288022400738221746015 6388932033601107332619023)
          ·
            refine ⟨9583398050401660998928535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6388932033601107332619023 9583398050401660998928535)
            ·
              refine ⟨14375097075602491498392803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9583398050401660998928535 14375097075602491498392803)
              ·
                refine ⟨21562645613403737247589205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14375097075602491498392803 21562645613403737247589205)
                ·
                  refine ⟨126343626641037522935093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21562645613403737247589205 126343626641037522935093)
                  ·
                    rfl

theorem cell20_276810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_276810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276810 prefixEnd_276810 := by exact prefixLift 276810
  have htrace : WordTrace (prefixWord ++ tailWord_276810) baseStart_276810 baseEnd_276810 := by
    simpa [prefixWord, tailWord_276810, baseEnd_276810] using wordTrace_append hprefix tailTrace_276810
  have hstable : (prefixWord ++ tailWord_276810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276810).length < 2 ^ (prefixWord ++ tailWord_276810).sum := by decide
  have hdescent : baseEnd_276810 < baseStart_276810 := by decide
  rcases family_descends (prefixWord ++ tailWord_276810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276872 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_276872 : Nat := 118140960795 + 276872 * 2 ^ 59
def prefixEnd_276872 : Nat := 4983230072969 + 3 ^ 40 * 276872 * 2
def baseEnd_276872 : Nat := 126371925130440862868173

theorem tailTrace_276872 : CollatzResearch.WordTrace tailWord_276872 prefixEnd_276872 126371925130440862868173 := by
  unfold tailWord_276872
  simp only [CollatzResearch.WordTrace]
  refine ⟨5049175726473752409040435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6732234301965003212053913 5049175726473752409040435)
  ·
    refine ⟨7573763589710628613560653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5049175726473752409040435 7573763589710628613560653)
    ·
      refine ⟨2840161346141485730085245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7573763589710628613560653 2840161346141485730085245)
      ·
        refine ⟨1065060504803057148781967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2840161346141485730085245 1065060504803057148781967)
        ·
          refine ⟨1597590757204585723172951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065060504803057148781967 1597590757204585723172951)
          ·
            refine ⟨2396386135806878584759427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597590757204585723172951 2396386135806878584759427)
            ·
              refine ⟨3594579203710317877139141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396386135806878584759427 3594579203710317877139141)
              ·
                refine ⟨673983600695684601963589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3594579203710317877139141 673983600695684601963589)
                ·
                  refine ⟨126371925130440862868173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 673983600695684601963589 126371925130440862868173)
                  ·
                    rfl

theorem cell20_276872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_276872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276872 prefixEnd_276872 := by exact prefixLift 276872
  have htrace : WordTrace (prefixWord ++ tailWord_276872) baseStart_276872 baseEnd_276872 := by
    simpa [prefixWord, tailWord_276872, baseEnd_276872] using wordTrace_append hprefix tailTrace_276872
  have hstable : (prefixWord ++ tailWord_276872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276872).length < 2 ^ (prefixWord ++ tailWord_276872).sum := by decide
  have hdescent : baseEnd_276872 < baseStart_276872 := by decide
  rcases family_descends (prefixWord ++ tailWord_276872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276903 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_276903 : Nat := 118140960795 + 276903 * 2 ^ 59
def prefixEnd_276903 : Nat := 4983230072969 + 3 ^ 40 * 276903 * 2
def baseEnd_276903 : Nat := 126386074375142532834713

theorem tailTrace_276903 : CollatzResearch.WordTrace tailWord_276903 prefixEnd_276903 126386074375142532834713 := by
  unfold tailWord_276903
  simp only [CollatzResearch.WordTrace]
  refine ⟨10099482115835197112459363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6732988077223464741639575 10099482115835197112459363)
  ·
    refine ⟨15149223173752795668689045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10099482115835197112459363 15149223173752795668689045)
    ·
      refine ⟨710119836269662296969799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15149223173752795668689045 710119836269662296969799)
      ·
        refine ⟨1065179754404493445454699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710119836269662296969799 1065179754404493445454699)
        ·
          refine ⟨1597769631606740168182049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065179754404493445454699 1597769631606740168182049)
          ·
            refine ⟨1198327223705055126136537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1597769631606740168182049 1198327223705055126136537)
            ·
              refine ⟨898745417778791344602403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1198327223705055126136537 898745417778791344602403)
              ·
                refine ⟨1348118126668187016903605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898745417778791344602403 1348118126668187016903605)
                ·
                  refine ⟨126386074375142532834713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1348118126668187016903605 126386074375142532834713)
                  ·
                    rfl

theorem cell20_276903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_276903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276903 prefixEnd_276903 := by exact prefixLift 276903
  have htrace : WordTrace (prefixWord ++ tailWord_276903) baseStart_276903 baseEnd_276903 := by
    simpa [prefixWord, tailWord_276903, baseEnd_276903] using wordTrace_append hprefix tailTrace_276903
  have hstable : (prefixWord ++ tailWord_276903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276903).length < 2 ^ (prefixWord ++ tailWord_276903).sum := by decide
  have hdescent : baseEnd_276903 < baseStart_276903 := by decide
  rcases family_descends (prefixWord ++ tailWord_276903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276916 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 3]
def baseStart_276916 : Nat := 118140960795 + 276916 * 2 ^ 59
def prefixEnd_276916 : Nat := 4983230072969 + 3 ^ 40 * 276916 * 2
def baseEnd_276916 : Nat := 126392007929372265401327

theorem tailTrace_276916 : CollatzResearch.WordTrace tailWord_276916 prefixEnd_276916 126392007929372265401327 := by
  unfold tailWord_276916
  simp only [CollatzResearch.WordTrace]
  refine ⟨5049978132394050166341301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6733304176525400221788401 5049978132394050166341301)
  ·
    refine ⟨473435449911942203094497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5049978132394050166341301 473435449911942203094497)
    ·
      refine ⟨355076587433956652320873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 473435449911942203094497 355076587433956652320873)
      ·
        refine ⟨266307440575467489240655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355076587433956652320873 266307440575467489240655)
        ·
          refine ⟨399461160863201233860983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266307440575467489240655 399461160863201233860983)
          ·
            refine ⟨599191741294801850791475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399461160863201233860983 599191741294801850791475)
            ·
              refine ⟨898787611942202776187213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599191741294801850791475 898787611942202776187213)
              ·
                refine ⟨337045354478326041070205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 898787611942202776187213 337045354478326041070205)
                ·
                  refine ⟨126392007929372265401327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337045354478326041070205 126392007929372265401327)
                  ·
                    rfl

theorem cell20_276916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_276916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276916 prefixEnd_276916 := by exact prefixLift 276916
  have htrace : WordTrace (prefixWord ++ tailWord_276916) baseStart_276916 baseEnd_276916 := by
    simpa [prefixWord, tailWord_276916, baseEnd_276916] using wordTrace_append hprefix tailTrace_276916
  have hstable : (prefixWord ++ tailWord_276916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276916).length < 2 ^ (prefixWord ++ tailWord_276916).sum := by decide
  have hdescent : baseEnd_276916 < baseStart_276916 := by decide
  rcases family_descends (prefixWord ++ tailWord_276916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276931 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_276931 : Nat := 118140960795 + 276931 * 2 ^ 59
def prefixEnd_276931 : Nat := 4983230072969 + 3 ^ 40 * 276931 * 2
def baseEnd_276931 : Nat := 126398854338098879901265

theorem tailTrace_276931 : CollatzResearch.WordTrace tailWord_276931 prefixEnd_276931 126398854338098879901265 := by
  unfold tailWord_276931
  simp only [CollatzResearch.WordTrace]
  refine ⟨10100503359733757894478647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6733668906489171929652431 10100503359733757894478647)
  ·
    refine ⟨15150755039600636841717971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10100503359733757894478647 15150755039600636841717971)
    ·
      refine ⟨22726132559400955262576957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15150755039600636841717971 22726132559400955262576957)
      ·
        refine ⟨8522299709775358223466359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22726132559400955262576957 8522299709775358223466359)
        ·
          refine ⟨12783449564663037335199539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8522299709775358223466359 12783449564663037335199539)
          ·
            refine ⟨19175174346994556002799309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12783449564663037335199539 19175174346994556002799309)
            ·
              refine ⟨7190690380122958501049741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19175174346994556002799309 7190690380122958501049741)
              ·
                refine ⟨2696508892546109437893653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7190690380122958501049741 2696508892546109437893653)
                ·
                  refine ⟨126398854338098879901265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2696508892546109437893653 126398854338098879901265)
                  ·
                    rfl

theorem cell20_276931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_276931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_276931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_276931 prefixEnd_276931 := by exact prefixLift 276931
  have htrace : WordTrace (prefixWord ++ tailWord_276931) baseStart_276931 baseEnd_276931 := by
    simpa [prefixWord, tailWord_276931, baseEnd_276931] using wordTrace_append hprefix tailTrace_276931
  have hstable : (prefixWord ++ tailWord_276931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276931).length < 2 ^ (prefixWord ++ tailWord_276931).sum := by decide
  have hdescent : baseEnd_276931 < baseStart_276931 := by decide
  rcases family_descends (prefixWord ++ tailWord_276931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277000 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_277000 : Nat := 118140960795 + 277000 * 2 ^ 59
def prefixEnd_277000 : Nat := 4983230072969 + 3 ^ 40 * 277000 * 2
def baseEnd_277000 : Nat := 126430347818241306600983

theorem tailTrace_277000 : CollatzResearch.WordTrace tailWord_277000 prefixEnd_277000 126430347818241306600983 := by
  unfold tailWord_277000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051509998241891339370227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6735346664322521785826969 5051509998241891339370227)
  ·
    refine ⟨7577264997362837009055341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5051509998241891339370227 7577264997362837009055341)
    ·
      refine ⟨2841474374011063878395753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7577264997362837009055341 2841474374011063878395753)
      ·
        refine ⟨2131105780508297908796815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2841474374011063878395753 2131105780508297908796815)
        ·
          refine ⟨3196658670762446863195223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2131105780508297908796815 3196658670762446863195223)
          ·
            refine ⟨4794988006143670294792835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196658670762446863195223 4794988006143670294792835)
            ·
              refine ⟨7192482009215505442189253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4794988006143670294792835 7192482009215505442189253)
              ·
                refine ⟨1348590376727907270410485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7192482009215505442189253 1348590376727907270410485)
                ·
                  refine ⟨126430347818241306600983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1348590376727907270410485 126430347818241306600983)
                  ·
                    rfl

theorem cell20_277000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_277000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277000 prefixEnd_277000 := by exact prefixLift 277000
  have htrace : WordTrace (prefixWord ++ tailWord_277000) baseStart_277000 baseEnd_277000 := by
    simpa [prefixWord, tailWord_277000, baseEnd_277000] using wordTrace_append hprefix tailTrace_277000
  have hstable : (prefixWord ++ tailWord_277000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277000).length < 2 ^ (prefixWord ++ tailWord_277000).sum := by decide
  have hdescent : baseEnd_277000 < baseStart_277000 := by decide
  rcases family_descends (prefixWord ++ tailWord_277000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277003 : List Nat := [1, 1, 1, 1, 7, 1, 1, 5, 2]
def baseStart_277003 : Nat := 118140960795 + 277003 * 2 ^ 59
def prefixEnd_277003 : Nat := 4983230072969 + 3 ^ 40 * 277003 * 2
def baseEnd_277003 : Nat := 126431717099986629500971

theorem tailTrace_277003 : CollatzResearch.WordTrace tailWord_277003 prefixEnd_277003 126431717099986629500971 := by
  unfold tailWord_277003
  simp only [CollatzResearch.WordTrace]
  refine ⟨10103129415472914191099663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6735419610315276127399775 10103129415472914191099663)
  ·
    refine ⟨15154694123209371286649495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10103129415472914191099663 15154694123209371286649495)
    ·
      refine ⟨22732041184814056929974243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15154694123209371286649495 22732041184814056929974243)
      ·
        refine ⟨34098061777221085394961365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22732041184814056929974243 34098061777221085394961365)
        ·
          refine ⟨799173322903619188944407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 34098061777221085394961365 799173322903619188944407)
          ·
            refine ⟨1198759984355428783416611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799173322903619188944407 1198759984355428783416611)
            ·
              refine ⟨1798139976533143175124917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198759984355428783416611 1798139976533143175124917)
              ·
                refine ⟨168575622799982172667961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1798139976533143175124917 168575622799982172667961)
                ·
                  refine ⟨126431717099986629500971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168575622799982172667961 126431717099986629500971)
                  ·
                    rfl

theorem cell20_277003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 2].length) (baseStart_277003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277003 prefixEnd_277003 := by exact prefixLift 277003
  have htrace : WordTrace (prefixWord ++ tailWord_277003) baseStart_277003 baseEnd_277003 := by
    simpa [prefixWord, tailWord_277003, baseEnd_277003] using wordTrace_append hprefix tailTrace_277003
  have hstable : (prefixWord ++ tailWord_277003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277003).length < 2 ^ (prefixWord ++ tailWord_277003).sum := by decide
  have hdescent : baseEnd_277003 < baseStart_277003 := by decide
  rcases family_descends (prefixWord ++ tailWord_277003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277054 : List Nat := [4, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_277054 : Nat := 118140960795 + 277054 * 2 ^ 59
def prefixEnd_277054 : Nat := 4983230072969 + 3 ^ 40 * 277054 * 2
def baseEnd_277054 : Nat := 126454994889657118800763

theorem tailTrace_277054 : CollatzResearch.WordTrace tailWord_277054 prefixEnd_277054 126454994889657118800763 := by
  unfold tailWord_277054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263123692286018737650777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6736659692192099934137477 1263123692286018737650777)
  ·
    refine ⟨947342769214514053238083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1263123692286018737650777 947342769214514053238083)
    ·
      refine ⟨1421014153821771079857125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 947342769214514053238083 1421014153821771079857125)
      ·
        refine ⟨266440153841582077473211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1421014153821771079857125 266440153841582077473211)
        ·
          refine ⟨399660230762373116209817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266440153841582077473211 399660230762373116209817)
          ·
            refine ⟨299745173071779837157363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399660230762373116209817 299745173071779837157363)
            ·
              refine ⟨449617759607669755736045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299745173071779837157363 449617759607669755736045)
              ·
                refine ⟨168606659852876158401017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 449617759607669755736045 168606659852876158401017)
                ·
                  refine ⟨126454994889657118800763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168606659852876158401017 126454994889657118800763)
                  ·
                    rfl

theorem cell20_277054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_277054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277054 prefixEnd_277054 := by exact prefixLift 277054
  have htrace : WordTrace (prefixWord ++ tailWord_277054) baseStart_277054 baseEnd_277054 := by
    simpa [prefixWord, tailWord_277054, baseEnd_277054] using wordTrace_append hprefix tailTrace_277054
  have hstable : (prefixWord ++ tailWord_277054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277054).length < 2 ^ (prefixWord ++ tailWord_277054).sum := by decide
  have hdescent : baseEnd_277054 < baseStart_277054 := by decide
  rcases family_descends (prefixWord ++ tailWord_277054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277128 : List Nat := [2, 1, 3, 14]
def baseStart_277128 : Nat := 118140960795 + 277128 * 2 ^ 59
def prefixEnd_277128 : Nat := 4983230072969 + 3 ^ 40 * 277128 * 2
def baseEnd_277128 : Nat := 520529919777949589851

theorem tailTrace_277128 : CollatzResearch.WordTrace tailWord_277128 prefixEnd_277128 520529919777949589851 := by
  unfold tailWord_277128
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053844270010030269700019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6738459026680040359600025 5053844270010030269700019)
  ·
    refine ⟨7580766405015045404550029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5053844270010030269700019 7580766405015045404550029)
    ·
      refine ⟨2842787401880642026706261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7580766405015045404550029 2842787401880642026706261)
      ·
        refine ⟨520529919777949589851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 2842787401880642026706261 520529919777949589851)
        ·
          rfl

theorem cell20_277128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 14].length) (baseStart_277128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277128 prefixEnd_277128 := by exact prefixLift 277128
  have htrace : WordTrace (prefixWord ++ tailWord_277128) baseStart_277128 baseEnd_277128 := by
    simpa [prefixWord, tailWord_277128, baseEnd_277128] using wordTrace_append hprefix tailTrace_277128
  have hstable : (prefixWord ++ tailWord_277128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277128).length < 2 ^ (prefixWord ++ tailWord_277128).sum := by decide
  have hdescent : baseEnd_277128 < baseStart_277128 := by decide
  rcases family_descends (prefixWord ++ tailWord_277128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277130 : List Nat := [3, 1, 2, 3, 4, 1, 2, 2, 2]
def baseStart_277130 : Nat := 118140960795 + 277130 * 2 ^ 59
def prefixEnd_277130 : Nat := 4983230072969 + 3 ^ 40 * 277130 * 2
def baseEnd_277130 : Nat := 126489683360538632267119

theorem tailTrace_277130 : CollatzResearch.WordTrace tailWord_277130 prefixEnd_277130 126489683360538632267119 := by
  unfold tailWord_277130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526940371503203720243211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6738507657341876587315229 2526940371503203720243211)
  ·
    refine ⟨3790410557254805580364817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2526940371503203720243211 3790410557254805580364817)
    ·
      refine ⟨2842807917941104185273613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3790410557254805580364817 2842807917941104185273613)
      ·
        refine ⟨1066052969227914069477605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2842807917941104185273613 1066052969227914069477605)
        ·
          refine ⟨199884931730233888027051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1066052969227914069477605 199884931730233888027051)
          ·
            refine ⟨299827397595350832040577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199884931730233888027051 299827397595350832040577)
            ·
              refine ⟨224870548196513124030433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299827397595350832040577 224870548196513124030433)
              ·
                refine ⟨168652911147384843022825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224870548196513124030433 168652911147384843022825)
                ·
                  refine ⟨126489683360538632267119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168652911147384843022825 126489683360538632267119)
                  ·
                    rfl

theorem cell20_277130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_277130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277130 prefixEnd_277130 := by exact prefixLift 277130
  have htrace : WordTrace (prefixWord ++ tailWord_277130) baseStart_277130 baseEnd_277130 := by
    simpa [prefixWord, tailWord_277130, baseEnd_277130] using wordTrace_append hprefix tailTrace_277130
  have hstable : (prefixWord ++ tailWord_277130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277130).length < 2 ^ (prefixWord ++ tailWord_277130).sum := by decide
  have hdescent : baseEnd_277130 < baseStart_277130 := by decide
  rcases family_descends (prefixWord ++ tailWord_277130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277221 : List Nat := [1, 3, 1, 4, 1, 3, 1, 6]
def baseStart_277221 : Nat := 118140960795 + 277221 * 2 ^ 59
def prefixEnd_277221 : Nat := 4983230072969 + 3 ^ 40 * 277221 * 2
def baseEnd_277221 : Nat := 42177072746715586744471

theorem tailTrace_277221 : CollatzResearch.WordTrace tailWord_277221 prefixEnd_277221 42177072746715586744471 := by
  unfold tailWord_277221
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111080528683137422535517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6740720352455424948357011 10111080528683137422535517)
  ·
    refine ⟨3791655198256176533450819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10111080528683137422535517 3791655198256176533450819)
    ·
      refine ⟨5687482797384264800176229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3791655198256176533450819 5687482797384264800176229)
      ·
        refine ⟨1066403024509549650033043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5687482797384264800176229 1066403024509549650033043)
        ·
          refine ⟨1599604536764324475049565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066403024509549650033043 1599604536764324475049565)
          ·
            refine ⟨599851701286621678143587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1599604536764324475049565 599851701286621678143587)
            ·
              refine ⟨899777551929932517215381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599851701286621678143587 899777551929932517215381)
              ·
                refine ⟨42177072746715586744471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 899777551929932517215381 42177072746715586744471)
                ·
                  rfl

theorem cell20_277221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_277221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277221 prefixEnd_277221 := by exact prefixLift 277221
  have htrace : WordTrace (prefixWord ++ tailWord_277221) baseStart_277221 baseEnd_277221 := by
    simpa [prefixWord, tailWord_277221, baseEnd_277221] using wordTrace_append hprefix tailTrace_277221
  have hstable : (prefixWord ++ tailWord_277221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277221).length < 2 ^ (prefixWord ++ tailWord_277221).sum := by decide
  have hdescent : baseEnd_277221 < baseStart_277221 := by decide
  rcases family_descends (prefixWord ++ tailWord_277221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277231 : List Nat := [1, 1, 2, 1, 5, 2, 3, 3, 2]
def baseStart_277231 : Nat := 118140960795 + 277231 * 2 ^ 59
def prefixEnd_277231 : Nat := 4983230072969 + 3 ^ 40 * 277231 * 2
def baseEnd_277231 : Nat := 126535782512631169900039

theorem tailTrace_277231 : CollatzResearch.WordTrace tailWord_277231 prefixEnd_277231 126535782512631169900039 := by
  unfold tailWord_277231
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111445258646909130399547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6740963505764606086933031 10111445258646909130399547)
  ·
    refine ⟨15167167887970363695599321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10111445258646909130399547 15167167887970363695599321)
    ·
      refine ⟨11375375915977772771699491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15167167887970363695599321 11375375915977772771699491)
      ·
        refine ⟨17063063873966659157549237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11375375915977772771699491 17063063873966659157549237)
        ·
          refine ⟨1599662238184374296020241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17063063873966659157549237 1599662238184374296020241)
          ·
            refine ⟨1199746678638280722015181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1599662238184374296020241 1199746678638280722015181)
            ·
              refine ⟨449905004489355270755693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1199746678638280722015181 449905004489355270755693)
              ·
                refine ⟨168714376683508226533385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 449905004489355270755693 168714376683508226533385)
                ·
                  refine ⟨126535782512631169900039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168714376683508226533385 126535782512631169900039)
                  ·
                    rfl

theorem cell20_277231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 2].length) (baseStart_277231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277231 prefixEnd_277231 := by exact prefixLift 277231
  have htrace : WordTrace (prefixWord ++ tailWord_277231) baseStart_277231 baseEnd_277231 := by
    simpa [prefixWord, tailWord_277231, baseEnd_277231] using wordTrace_append hprefix tailTrace_277231
  have hstable : (prefixWord ++ tailWord_277231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277231).length < 2 ^ (prefixWord ++ tailWord_277231).sum := by decide
  have hdescent : baseEnd_277231 < baseStart_277231 := by decide
  rcases family_descends (prefixWord ++ tailWord_277231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277242 : List Nat := [3, 1, 1, 1, 1, 3, 10]
def baseStart_277242 : Nat := 118140960795 + 277242 * 2 ^ 59
def prefixEnd_277242 : Nat := 4983230072969 + 3 ^ 40 * 277242 * 2
def baseEnd_277242 : Nat := 14060089245818224503703

theorem tailTrace_277242 : CollatzResearch.WordTrace tailWord_277242 prefixEnd_277242 14060089245818224503703 := by
  unfold tailWord_277242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2527961615401764502262495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6741230974404705339366653 2527961615401764502262495)
  ·
    refine ⟨3791942423102646753393743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2527961615401764502262495 3791942423102646753393743)
    ·
      refine ⟨5687913634653970130090615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3791942423102646753393743 5687913634653970130090615)
      ·
        refine ⟨8531870451980955195135923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5687913634653970130090615 8531870451980955195135923)
        ·
          refine ⟨12797805677971432792703885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8531870451980955195135923 12797805677971432792703885)
          ·
            refine ⟨4799177129239287297263957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12797805677971432792703885 4799177129239287297263957)
            ·
              refine ⟨14060089245818224503703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4799177129239287297263957 14060089245818224503703)
              ·
                rfl

theorem cell20_277242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 10].length) (baseStart_277242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277242 prefixEnd_277242 := by exact prefixLift 277242
  have htrace : WordTrace (prefixWord ++ tailWord_277242) baseStart_277242 baseEnd_277242 := by
    simpa [prefixWord, tailWord_277242, baseEnd_277242] using wordTrace_append hprefix tailTrace_277242
  have hstable : (prefixWord ++ tailWord_277242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277242).length < 2 ^ (prefixWord ++ tailWord_277242).sum := by decide
  have hdescent : baseEnd_277242 < baseStart_277242 := by decide
  rcases family_descends (prefixWord ++ tailWord_277242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277293 : List Nat := [1, 5, 3, 2, 2, 7]
def baseStart_277293 : Nat := 118140960795 + 277293 * 2 ^ 59
def prefixEnd_277293 : Nat := 4983230072969 + 3 ^ 40 * 277293 * 2
def baseEnd_277293 : Nat := 4687558555630907771597

theorem tailTrace_277293 : CollatzResearch.WordTrace tailWord_277293 prefixEnd_277293 4687558555630907771597 := by
  unfold tailWord_277293
  simp only [CollatzResearch.WordTrace]
  refine ⟨10113706584422293719156533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6742471056281529146104355 10113706584422293719156533)
  ·
    refine ⟨948159992289590036170925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10113706584422293719156533 948159992289590036170925)
    ·
      refine ⟨355559997108596263564097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 948159992289590036170925 355559997108596263564097)
      ·
        refine ⟨266669997831447197673073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355559997108596263564097 266669997831447197673073)
        ·
          refine ⟨200002498373585398254805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266669997831447197673073 200002498373585398254805)
          ·
            refine ⟨4687558555630907771597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 200002498373585398254805 4687558555630907771597)
            ·
              rfl

theorem cell20_277293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 7].length) (baseStart_277293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277293 prefixEnd_277293 := by exact prefixLift 277293
  have htrace : WordTrace (prefixWord ++ tailWord_277293) baseStart_277293 baseEnd_277293 := by
    simpa [prefixWord, tailWord_277293, baseEnd_277293] using wordTrace_append hprefix tailTrace_277293
  have hstable : (prefixWord ++ tailWord_277293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277293).length < 2 ^ (prefixWord ++ tailWord_277293).sum := by decide
  have hdescent : baseEnd_277293 < baseStart_277293 := by decide
  rcases family_descends (prefixWord ++ tailWord_277293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277356 : List Nat := [2, 2, 1, 1, 4, 1, 9]
def baseStart_277356 : Nat := 118140960795 + 277356 * 2 ^ 59
def prefixEnd_277356 : Nat := 4983230072969 + 3 ^ 40 * 277356 * 2
def baseEnd_277356 : Nat := 14065870657631810081429

theorem tailTrace_277356 : CollatzResearch.WordTrace tailWord_277356 prefixEnd_277356 14065870657631810081429 := by
  unfold tailWord_277356
  simp only [CollatzResearch.WordTrace]
  refine ⟨5058002191597027739349961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6744002922129370319133281 5058002191597027739349961)
  ·
    refine ⟨3793501643697770804512471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5058002191597027739349961 3793501643697770804512471)
    ·
      refine ⟨5690252465546656206768707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3793501643697770804512471 5690252465546656206768707)
      ·
        refine ⟨8535378698319984310153061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5690252465546656206768707 8535378698319984310153061)
        ·
          refine ⟨1600383505934997058153699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8535378698319984310153061 1600383505934997058153699)
          ·
            refine ⟨2400575258902495587230549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600383505934997058153699 2400575258902495587230549)
            ·
              refine ⟨14065870657631810081429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2400575258902495587230549 14065870657631810081429)
              ·
                rfl

theorem cell20_277356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 9].length) (baseStart_277356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277356 prefixEnd_277356 := by exact prefixLift 277356
  have htrace : WordTrace (prefixWord ++ tailWord_277356) baseStart_277356 baseEnd_277356 := by
    simpa [prefixWord, tailWord_277356, baseEnd_277356] using wordTrace_append hprefix tailTrace_277356
  have hstable : (prefixWord ++ tailWord_277356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277356).length < 2 ^ (prefixWord ++ tailWord_277356).sum := by decide
  have hdescent : baseEnd_277356 < baseStart_277356 := by decide
  rcases family_descends (prefixWord ++ tailWord_277356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277387 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_277387 : Nat := 118140960795 + 277387 * 2 ^ 59
def prefixEnd_277387 : Nat := 4983230072969 + 3 ^ 40 * 277387 * 2
def baseEnd_277387 : Nat := 126606985163387960699401

theorem tailTrace_277387 : CollatzResearch.WordTrace tailWord_277387 prefixEnd_277387 126606985163387960699401 := by
  unfold tailWord_277387
  simp only [CollatzResearch.WordTrace]
  refine ⟨10117135046081747773078415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6744756697387831848718943 10117135046081747773078415)
  ·
    refine ⟨15175702569122621659617623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10117135046081747773078415 15175702569122621659617623)
    ·
      refine ⟨22763553853683932489426435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15175702569122621659617623 22763553853683932489426435)
      ·
        refine ⟨34145330780525898734139653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22763553853683932489426435 34145330780525898734139653)
        ·
          refine ⟨6402249521348606012651185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34145330780525898734139653 6402249521348606012651185)
          ·
            refine ⟨4801687141011454509488389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6402249521348606012651185 4801687141011454509488389)
            ·
              refine ⟨900316338939647720529073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4801687141011454509488389 900316338939647720529073)
              ·
                refine ⟨675237254204735790396805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900316338939647720529073 675237254204735790396805)
                ·
                  refine ⟨126606985163387960699401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 675237254204735790396805 126606985163387960699401)
                  ·
                    rfl

theorem cell20_277387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_277387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277387 prefixEnd_277387 := by exact prefixLift 277387
  have htrace : WordTrace (prefixWord ++ tailWord_277387) baseStart_277387 baseEnd_277387 := by
    simpa [prefixWord, tailWord_277387, baseEnd_277387] using wordTrace_append hprefix tailTrace_277387
  have hstable : (prefixWord ++ tailWord_277387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277387).length < 2 ^ (prefixWord ++ tailWord_277387).sum := by decide
  have hdescent : baseEnd_277387 < baseStart_277387 := by decide
  rcases family_descends (prefixWord ++ tailWord_277387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277428 : List Nat := [2, 5, 2, 1, 1, 1, 1, 7]
def baseStart_277428 : Nat := 118140960795 + 277428 * 2 ^ 59
def prefixEnd_277428 : Nat := 4983230072969 + 3 ^ 40 * 277428 * 2
def baseEnd_277428 : Nat := 42208566226858013444189

theorem tailTrace_277428 : CollatzResearch.WordTrace tailWord_277428 prefixEnd_277428 42208566226858013444189 := by
  unfold tailWord_277428
  simp only [CollatzResearch.WordTrace]
  refine ⟨5059315219466605887660469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6745753625955474516880625 5059315219466605887660469)
  ·
    refine ⟨474310801824994301968169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5059315219466605887660469 474310801824994301968169)
    ·
      refine ⟨355733101368745726476127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 474310801824994301968169 355733101368745726476127)
      ·
        refine ⟨533599652053118589714191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355733101368745726476127 533599652053118589714191)
        ·
          refine ⟨800399478079677884571287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533599652053118589714191 800399478079677884571287)
          ·
            refine ⟨1200599217119516826856931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800399478079677884571287 1200599217119516826856931)
            ·
              refine ⟨1800898825679275240285397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200599217119516826856931 1800898825679275240285397)
              ·
                refine ⟨42208566226858013444189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1800898825679275240285397 42208566226858013444189)
                ·
                  rfl

theorem cell20_277428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_277428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277428 prefixEnd_277428 := by exact prefixLift 277428
  have htrace : WordTrace (prefixWord ++ tailWord_277428) baseStart_277428 baseEnd_277428 := by
    simpa [prefixWord, tailWord_277428, baseEnd_277428] using wordTrace_append hprefix tailTrace_277428
  have hstable : (prefixWord ++ tailWord_277428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277428).length < 2 ^ (prefixWord ++ tailWord_277428).sum := by decide
  have hdescent : baseEnd_277428 < baseStart_277428 := by decide
  rcases family_descends (prefixWord ++ tailWord_277428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277432 : List Nat := [2, 1, 2, 1, 2, 4, 1, 7]
def baseStart_277432 : Nat := 118140960795 + 277432 * 2 ^ 59
def prefixEnd_277432 : Nat := 4983230072969 + 3 ^ 40 * 277432 * 2
def baseEnd_277432 : Nat := 42209174796522601399739

theorem tailTrace_277432 : CollatzResearch.WordTrace tailWord_277432 prefixEnd_277432 42209174796522601399739 := by
  unfold tailWord_277432
  simp only [CollatzResearch.WordTrace]
  refine ⟨5059388165459360229233275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6745850887279146972311033 5059388165459360229233275)
  ·
    refine ⟨7589082248189040343849913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5059388165459360229233275 7589082248189040343849913)
    ·
      refine ⟨5691811686141780257887435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7589082248189040343849913 5691811686141780257887435)
      ·
        refine ⟨8537717529212670386831153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5691811686141780257887435 8537717529212670386831153)
        ·
          refine ⟨6403288146909502790123365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8537717529212670386831153 6403288146909502790123365)
          ·
            refine ⟨1200616527545531773148131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6403288146909502790123365 1200616527545531773148131)
            ·
              refine ⟨1800924791318297659722197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200616527545531773148131 1800924791318297659722197)
              ·
                refine ⟨42209174796522601399739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1800924791318297659722197 42209174796522601399739)
                ·
                  rfl

theorem cell20_277432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_277432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277432 prefixEnd_277432 := by exact prefixLift 277432
  have htrace : WordTrace (prefixWord ++ tailWord_277432) baseStart_277432 baseEnd_277432 := by
    simpa [prefixWord, tailWord_277432, baseEnd_277432] using wordTrace_append hprefix tailTrace_277432
  have hstable : (prefixWord ++ tailWord_277432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277432).length < 2 ^ (prefixWord ++ tailWord_277432).sum := by decide
  have hdescent : baseEnd_277432 < baseStart_277432 := by decide
  rcases family_descends (prefixWord ++ tailWord_277432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277439 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_277439 : Nat := 118140960795 + 277439 * 2 ^ 59
def prefixEnd_277439 : Nat := 4983230072969 + 3 ^ 40 * 277439 * 2
def baseEnd_277439 : Nat := 126630719380306890965855

theorem tailTrace_277439 : CollatzResearch.WordTrace tailWord_277439 prefixEnd_277439 126630719380306890965855 := by
  unfold tailWord_277439
  simp only [CollatzResearch.WordTrace]
  refine ⟨10119031641893360653971371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6746021094595573769314247 10119031641893360653971371)
  ·
    refine ⟨15178547462840040980957057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10119031641893360653971371 15178547462840040980957057)
    ·
      refine ⟨11383910597130030735717793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15178547462840040980957057 11383910597130030735717793)
      ·
        refine ⟨8537932947847523051788345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11383910597130030735717793 8537932947847523051788345)
        ·
          refine ⟨6403449710885642288841259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8537932947847523051788345 6403449710885642288841259)
          ·
            refine ⟨9605174566328463433261889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6403449710885642288841259 9605174566328463433261889)
            ·
              refine ⟨7203880924746347574946417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9605174566328463433261889 7203880924746347574946417)
              ·
                refine ⟨5402910693559760681209813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7203880924746347574946417 5402910693559760681209813)
                ·
                  refine ⟨126630719380306890965855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5402910693559760681209813 126630719380306890965855)
                  ·
                    rfl

theorem cell20_277439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_277439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277439 prefixEnd_277439 := by exact prefixLift 277439
  have htrace : WordTrace (prefixWord ++ tailWord_277439) baseStart_277439 baseEnd_277439 := by
    simpa [prefixWord, tailWord_277439, baseEnd_277439] using wordTrace_append hprefix tailTrace_277439
  have hstable : (prefixWord ++ tailWord_277439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277439).length < 2 ^ (prefixWord ++ tailWord_277439).sum := by decide
  have hdescent : baseEnd_277439 < baseStart_277439 := by decide
  rcases family_descends (prefixWord ++ tailWord_277439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277487 : List Nat := [1, 1, 2, 1, 4, 5, 1, 5]
def baseStart_277487 : Nat := 118140960795 + 277487 * 2 ^ 59
def prefixEnd_277487 : Nat := 4983230072969 + 3 ^ 40 * 277487 * 2
def baseEnd_277487 : Nat := 42217542629410685788553

theorem tailTrace_277487 : CollatzResearch.WordTrace tailWord_277487 prefixEnd_277487 42217542629410685788553 := by
  unfold tailWord_277487
  simp only [CollatzResearch.WordTrace]
  refine ⟨10120782345719464851718715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6747188230479643234479143 10120782345719464851718715)
  ·
    refine ⟨15181173518579197277578073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10120782345719464851718715 15181173518579197277578073)
    ·
      refine ⟨11385880138934397958183555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15181173518579197277578073 11385880138934397958183555)
      ·
        refine ⟨17078820208401596937275333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11385880138934397958183555 17078820208401596937275333)
        ·
          refine ⟨3202278789075299425739125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17078820208401596937275333 3202278789075299425739125)
          ·
            refine ⟨300213636475809321163043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3202278789075299425739125 300213636475809321163043)
            ·
              refine ⟨450320454713713981744565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300213636475809321163043 450320454713713981744565)
              ·
                refine ⟨42217542629410685788553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 450320454713713981744565 42217542629410685788553)
                ·
                  rfl

theorem cell20_277487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 5].length) (baseStart_277487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277487 prefixEnd_277487 := by exact prefixLift 277487
  have htrace : WordTrace (prefixWord ++ tailWord_277487) baseStart_277487 baseEnd_277487 := by
    simpa [prefixWord, tailWord_277487, baseEnd_277487] using wordTrace_append hprefix tailTrace_277487
  have hstable : (prefixWord ++ tailWord_277487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277487).length < 2 ^ (prefixWord ++ tailWord_277487).sum := by decide
  have hdescent : baseEnd_277487 < baseStart_277487 := by decide
  rcases family_descends (prefixWord ++ tailWord_277487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277539 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_277539 : Nat := 118140960795 + 277539 * 2 ^ 59
def prefixEnd_277539 : Nat := 4983230072969 + 3 ^ 40 * 277539 * 2
def baseEnd_277539 : Nat := 126676362105150987632113

theorem tailTrace_277539 : CollatzResearch.WordTrace tailWord_277539 prefixEnd_277539 126676362105150987632113 := by
  unfold tailWord_277539
  simp only [CollatzResearch.WordTrace]
  refine ⟨10122678941531077732611671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6748452627687385155074447 10122678941531077732611671)
  ·
    refine ⟨15184018412296616598917507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10122678941531077732611671 15184018412296616598917507)
    ·
      refine ⟨22776027618444924898376261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15184018412296616598917507 22776027618444924898376261)
      ·
        refine ⟨4270505178458423418445549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22776027618444924898376261 4270505178458423418445549)
        ·
          refine ⟨1601439441921908781917081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4270505178458423418445549 1601439441921908781917081)
          ·
            refine ⟨1201079581441431586437811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1601439441921908781917081 1201079581441431586437811)
            ·
              refine ⟨1801619372162147379656717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201079581441431586437811 1801619372162147379656717)
              ·
                refine ⟨675607264560805267371269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1801619372162147379656717 675607264560805267371269)
                ·
                  refine ⟨126676362105150987632113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 675607264560805267371269 126676362105150987632113)
                  ·
                    rfl

theorem cell20_277539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_277539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277539 prefixEnd_277539 := by exact prefixLift 277539
  have htrace : WordTrace (prefixWord ++ tailWord_277539) baseStart_277539 baseEnd_277539 := by
    simpa [prefixWord, tailWord_277539, baseEnd_277539] using wordTrace_append hprefix tailTrace_277539
  have hstable : (prefixWord ++ tailWord_277539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277539).length < 2 ^ (prefixWord ++ tailWord_277539).sum := by decide
  have hdescent : baseEnd_277539 < baseStart_277539 := by decide
  rcases family_descends (prefixWord ++ tailWord_277539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277569 : List Nat := [1, 2, 5, 1, 4, 1, 1, 3, 2]
def baseStart_277569 : Nat := 118140960795 + 277569 * 2 ^ 59
def prefixEnd_277569 : Nat := 4983230072969 + 3 ^ 40 * 277569 * 2
def baseEnd_277569 : Nat := 126690054922604216631991

theorem tailTrace_277569 : CollatzResearch.WordTrace tailWord_277569 prefixEnd_277569 126690054922604216631991 := by
  unfold tailWord_277569
  simp only [CollatzResearch.WordTrace]
  refine ⟨10123773131422392856203761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6749182087614928570802507 10123773131422392856203761)
  ·
    refine ⟨7592829848566794642152821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10123773131422392856203761 7592829848566794642152821)
    ·
      refine ⟨711827798303136997701827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7592829848566794642152821 711827798303136997701827)
      ·
        refine ⟨1067741697454705496552741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711827798303136997701827 1067741697454705496552741)
        ·
          refine ⟨200201568272757280603639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1067741697454705496552741 200201568272757280603639)
          ·
            refine ⟨300302352409135920905459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200201568272757280603639 300302352409135920905459)
            ·
              refine ⟨450453528613703881358189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300302352409135920905459 450453528613703881358189)
              ·
                refine ⟨168920073230138955509321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 450453528613703881358189 168920073230138955509321)
                ·
                  refine ⟨126690054922604216631991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168920073230138955509321 126690054922604216631991)
                  ·
                    rfl

theorem cell20_277569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_277569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277569 prefixEnd_277569 := by exact prefixLift 277569
  have htrace : WordTrace (prefixWord ++ tailWord_277569) baseStart_277569 baseEnd_277569 := by
    simpa [prefixWord, tailWord_277569, baseEnd_277569] using wordTrace_append hprefix tailTrace_277569
  have hstable : (prefixWord ++ tailWord_277569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277569).length < 2 ^ (prefixWord ++ tailWord_277569).sum := by decide
  have hdescent : baseEnd_277569 < baseStart_277569 := by decide
  rcases family_descends (prefixWord ++ tailWord_277569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277729 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_277729 : Nat := 118140960795 + 277729 * 2 ^ 59
def prefixEnd_277729 : Nat := 4983230072969 + 3 ^ 40 * 277729 * 2
def baseEnd_277729 : Nat := 126763083282354771298003

theorem tailTrace_277729 : CollatzResearch.WordTrace tailWord_277729 prefixEnd_277729 126763083282354771298003 := by
  unfold tailWord_277729
  simp only [CollatzResearch.WordTrace]
  refine ⟨10129608810842740182028241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6753072540561826788018827 10129608810842740182028241)
  ·
    refine ⟨7597206608132055136521181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10129608810842740182028241 7597206608132055136521181)
    ·
      refine ⟨2848952478049520676195443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7597206608132055136521181 2848952478049520676195443)
      ·
        refine ⟨4273428717074281014293165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848952478049520676195443 4273428717074281014293165)
        ·
          refine ⟨1602535768902855380359937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4273428717074281014293165 1602535768902855380359937)
          ·
            refine ⟨1201901826677141535269953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1602535768902855380359937 1201901826677141535269953)
            ·
              refine ⟨901426370007856151452465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1201901826677141535269953 901426370007856151452465)
              ·
                refine ⟨676069777505892113589349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 901426370007856151452465 676069777505892113589349)
                ·
                  refine ⟨126763083282354771298003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 676069777505892113589349 126763083282354771298003)
                  ·
                    rfl

theorem cell20_277729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_277729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277729 prefixEnd_277729 := by exact prefixLift 277729
  have htrace : WordTrace (prefixWord ++ tailWord_277729) baseStart_277729 baseEnd_277729 := by
    simpa [prefixWord, tailWord_277729, baseEnd_277729] using wordTrace_append hprefix tailTrace_277729
  have hstable : (prefixWord ++ tailWord_277729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277729).length < 2 ^ (prefixWord ++ tailWord_277729).sum := by decide
  have hdescent : baseEnd_277729 < baseStart_277729 := by decide
  rcases family_descends (prefixWord ++ tailWord_277729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277736 : List Nat := [2, 1, 4, 1, 2, 1, 3, 6]
def baseStart_277736 : Nat := 118140960795 + 277736 * 2 ^ 59
def prefixEnd_277736 : Nat := 4983230072969 + 3 ^ 40 * 277736 * 2
def baseEnd_277736 : Nat := 42255426091031286021547

theorem tailTrace_277736 : CollatzResearch.WordTrace tailWord_277736 prefixEnd_277736 42255426091031286021547 := by
  unfold tailWord_277736
  simp only [CollatzResearch.WordTrace]
  refine ⟨5064932060908690188766531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6753242747878253585022041 5064932060908690188766531)
  ·
    refine ⟨7597398091363035283149797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5064932060908690188766531 7597398091363035283149797)
    ·
      refine ⟨1424512142130569115590587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7597398091363035283149797 1424512142130569115590587)
      ·
        refine ⟨2136768213195853673385881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424512142130569115590587 2136768213195853673385881)
        ·
          refine ⟨1602576159896890255039411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2136768213195853673385881 1602576159896890255039411)
          ·
            refine ⟨2403864239845335382559117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602576159896890255039411 2403864239845335382559117)
            ·
              refine ⟨901449089942000768459669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2403864239845335382559117 901449089942000768459669)
              ·
                refine ⟨42255426091031286021547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 901449089942000768459669 42255426091031286021547)
                ·
                  rfl

theorem cell20_277736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_277736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277736 prefixEnd_277736 := by exact prefixLift 277736
  have htrace : WordTrace (prefixWord ++ tailWord_277736) baseStart_277736 baseEnd_277736 := by
    simpa [prefixWord, tailWord_277736, baseEnd_277736] using wordTrace_append hprefix tailTrace_277736
  have hstable : (prefixWord ++ tailWord_277736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277736).length < 2 ^ (prefixWord ++ tailWord_277736).sum := by decide
  have hdescent : baseEnd_277736 < baseStart_277736 := by decide
  rcases family_descends (prefixWord ++ tailWord_277736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277763 : List Nat := [1, 1, 1, 3, 2, 5, 3, 2, 2]
def baseStart_277763 : Nat := 118140960795 + 277763 * 2 ^ 59
def prefixEnd_277763 : Nat := 4983230072969 + 3 ^ 40 * 277763 * 2
def baseEnd_277763 : Nat := 126778601808801764164531

theorem tailTrace_277763 : CollatzResearch.WordTrace tailWord_277763 prefixEnd_277763 126778601808801764164531 := by
  unfold tailWord_277763
  simp only [CollatzResearch.WordTrace]
  refine ⟨10130848892719563988765943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6753899261813042659177295 10130848892719563988765943)
  ·
    refine ⟨15196273339079345983148915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10130848892719563988765943 15196273339079345983148915)
    ·
      refine ⟨22794410008619018974723373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15196273339079345983148915 22794410008619018974723373)
      ·
        refine ⟨8547903753232132115521265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22794410008619018974723373 8547903753232132115521265)
        ·
          refine ⟨6410927814924099086640949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8547903753232132115521265 6410927814924099086640949)
          ·
            refine ⟨601024482649134289372589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6410927814924099086640949 601024482649134289372589)
            ·
              refine ⟨225384180993425358514721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 601024482649134289372589 225384180993425358514721)
              ·
                refine ⟨169038135745069018886041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225384180993425358514721 169038135745069018886041)
                ·
                  refine ⟨126778601808801764164531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169038135745069018886041 126778601808801764164531)
                  ·
                    rfl

theorem cell20_277763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 2].length) (baseStart_277763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277763 prefixEnd_277763 := by exact prefixLift 277763
  have htrace : WordTrace (prefixWord ++ tailWord_277763) baseStart_277763 baseEnd_277763 := by
    simpa [prefixWord, tailWord_277763, baseEnd_277763] using wordTrace_append hprefix tailTrace_277763
  have hstable : (prefixWord ++ tailWord_277763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277763).length < 2 ^ (prefixWord ++ tailWord_277763).sum := by decide
  have hdescent : baseEnd_277763 < baseStart_277763 := by decide
  rcases family_descends (prefixWord ++ tailWord_277763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277774 : List Nat := [4, 1, 1, 2, 1, 3, 1, 7]
def baseStart_277774 : Nat := 118140960795 + 277774 * 2 ^ 59
def prefixEnd_277774 : Nat := 4983230072969 + 3 ^ 40 * 277774 * 2
def baseEnd_277774 : Nat := 42261207502844871599273

theorem tailTrace_277774 : CollatzResearch.WordTrace tailWord_277774 prefixEnd_277774 42261207502844871599273 := by
  unfold tailWord_277774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1266406261959964108427047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6754166730453141911610917 1266406261959964108427047)
  ·
    refine ⟨1899609392939946162640571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1266406261959964108427047 1899609392939946162640571)
    ·
      refine ⟨2849414089409919243960857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1899609392939946162640571 2849414089409919243960857)
      ·
        refine ⟨2137060567057439432970643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2849414089409919243960857 2137060567057439432970643)
        ·
          refine ⟨3205590850586159149455965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137060567057439432970643 3205590850586159149455965)
          ·
            refine ⟨1202096568969809681045987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3205590850586159149455965 1202096568969809681045987)
            ·
              refine ⟨1803144853454714521568981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202096568969809681045987 1803144853454714521568981)
              ·
                refine ⟨42261207502844871599273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1803144853454714521568981 42261207502844871599273)
                ·
                  rfl

theorem cell20_277774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_277774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277774 prefixEnd_277774 := by exact prefixLift 277774
  have htrace : WordTrace (prefixWord ++ tailWord_277774) baseStart_277774 baseEnd_277774 := by
    simpa [prefixWord, tailWord_277774, baseEnd_277774] using wordTrace_append hprefix tailTrace_277774
  have hstable : (prefixWord ++ tailWord_277774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277774).length < 2 ^ (prefixWord ++ tailWord_277774).sum := by decide
  have hdescent : baseEnd_277774 < baseStart_277774 := by decide
  rcases family_descends (prefixWord ++ tailWord_277774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277814 : List Nat := [5, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_277814 : Nat := 118140960795 + 277814 * 2 ^ 59
def prefixEnd_277814 : Nat := 4983230072969 + 3 ^ 40 * 277814 * 2
def baseEnd_277814 : Nat := 126801879598472253464323

theorem tailTrace_277814 : CollatzResearch.WordTrace tailWord_277814 prefixEnd_277814 126801879598472253464323 := by
  unfold tailWord_277814
  simp only [CollatzResearch.WordTrace]
  refine ⟨633294313470924981179531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6755139343689866465914997 633294313470924981179531)
  ·
    refine ⟨949941470206387471769297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 633294313470924981179531 949941470206387471769297)
    ·
      refine ⟨712456102654790603826973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 949941470206387471769297 712456102654790603826973)
      ·
        refine ⟨267171038495546476435115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 712456102654790603826973 267171038495546476435115)
        ·
          refine ⟨400756557743319714652673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267171038495546476435115 400756557743319714652673)
          ·
            refine ⟨300567418307489785989505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400756557743319714652673 300567418307489785989505)
            ·
              refine ⟨225425563730617339492129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300567418307489785989505 225425563730617339492129)
              ·
                refine ⟨169069172797963004619097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225425563730617339492129 169069172797963004619097)
                ·
                  refine ⟨126801879598472253464323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169069172797963004619097 126801879598472253464323)
                  ·
                    rfl

theorem cell20_277814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_277814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277814 prefixEnd_277814 := by exact prefixLift 277814
  have htrace : WordTrace (prefixWord ++ tailWord_277814) baseStart_277814 baseEnd_277814 := by
    simpa [prefixWord, tailWord_277814, baseEnd_277814] using wordTrace_append hprefix tailTrace_277814
  have hstable : (prefixWord ++ tailWord_277814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277814).length < 2 ^ (prefixWord ++ tailWord_277814).sum := by decide
  have hdescent : baseEnd_277814 < baseStart_277814 := by decide
  rcases family_descends (prefixWord ++ tailWord_277814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277836 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 3]
def baseStart_277836 : Nat := 118140960795 + 277836 * 2 ^ 59
def prefixEnd_277836 : Nat := 4983230072969 + 3 ^ 40 * 277836 * 2
def baseEnd_277836 : Nat := 126811920997937954730899

theorem tailTrace_277836 : CollatzResearch.WordTrace tailWord_277836 prefixEnd_277836 126811920997937954730899 := by
  unfold tailWord_277836
  simp only [CollatzResearch.WordTrace]
  refine ⟨5066755710727548728086681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6755674280970064970782241 5066755710727548728086681)
  ·
    refine ⟨3800066783045661546065011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5066755710727548728086681 3800066783045661546065011)
    ·
      refine ⟨5700100174568492319097517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3800066783045661546065011 5700100174568492319097517)
      ·
        refine ⟨2137537565463184619661569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5700100174568492319097517 2137537565463184619661569)
        ·
          refine ⟨1603153174097388464746177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2137537565463184619661569 1603153174097388464746177)
          ·
            refine ⟨1202364880573041348559633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1603153174097388464746177 1202364880573041348559633)
            ·
              refine ⟨901773660429781011419725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202364880573041348559633 901773660429781011419725)
              ·
                refine ⟨338165122661167879282397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 901773660429781011419725 338165122661167879282397)
                ·
                  refine ⟨126811920997937954730899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338165122661167879282397 126811920997937954730899)
                  ·
                    rfl

theorem cell20_277836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_277836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277836 prefixEnd_277836 := by exact prefixLift 277836
  have htrace : WordTrace (prefixWord ++ tailWord_277836) baseStart_277836 baseEnd_277836 := by
    simpa [prefixWord, tailWord_277836, baseEnd_277836] using wordTrace_append hprefix tailTrace_277836
  have hstable : (prefixWord ++ tailWord_277836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277836).length < 2 ^ (prefixWord ++ tailWord_277836).sum := by decide
  have hdescent : baseEnd_277836 < baseStart_277836 := by decide
  rcases family_descends (prefixWord ++ tailWord_277836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277860 : List Nat := [2, 3, 1, 1, 3, 2, 1, 5, 2]
def baseStart_277860 : Nat := 118140960795 + 277860 * 2 ^ 59
def prefixEnd_277860 : Nat := 4983230072969 + 3 ^ 40 * 277860 * 2
def baseEnd_277860 : Nat := 126822875251900537930801

theorem tailTrace_277860 : CollatzResearch.WordTrace tailWord_277860 prefixEnd_277860 126822875251900537930801 := by
  unfold tailWord_277860
  simp only [CollatzResearch.WordTrace]
  refine ⟨5067193386684074777523517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6756257848912099703364689 5067193386684074777523517)
  ·
    refine ⟨1900197520006528041571319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5067193386684074777523517 1900197520006528041571319)
    ·
      refine ⟨2850296280009792062356979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1900197520006528041571319 2850296280009792062356979)
      ·
        refine ⟨4275444420014688093535469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2850296280009792062356979 4275444420014688093535469)
        ·
          refine ⟨1603291657505508035075801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4275444420014688093535469 1603291657505508035075801)
          ·
            refine ⟨1202468743129131026306851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1603291657505508035075801 1202468743129131026306851)
            ·
              refine ⟨1803703114693696539460277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202468743129131026306851 1803703114693696539460277)
              ·
                refine ⟨169097167002534050574401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1803703114693696539460277 169097167002534050574401)
                ·
                  refine ⟨126822875251900537930801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169097167002534050574401 126822875251900537930801)
                  ·
                    rfl

theorem cell20_277860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_277860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277860 prefixEnd_277860 := by exact prefixLift 277860
  have htrace : WordTrace (prefixWord ++ tailWord_277860) baseStart_277860 baseEnd_277860 := by
    simpa [prefixWord, tailWord_277860, baseEnd_277860] using wordTrace_append hprefix tailTrace_277860
  have hstable : (prefixWord ++ tailWord_277860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277860).length < 2 ^ (prefixWord ++ tailWord_277860).sum := by decide
  have hdescent : baseEnd_277860 < baseStart_277860 := by decide
  rcases family_descends (prefixWord ++ tailWord_277860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277871 : List Nat := [1, 1, 2, 1, 3, 1, 11]
def baseStart_277871 : Nat := 118140960795 + 277871 * 2 ^ 59
def prefixEnd_277871 : Nat := 4983230072969 + 3 ^ 40 * 277871 * 2
def baseEnd_277871 : Nat := 14091988439070376507121

theorem tailTrace_277871 : CollatzResearch.WordTrace tailWord_277871 prefixEnd_277871 14091988439070376507121 := by
  unfold tailWord_277871
  simp only [CollatzResearch.WordTrace]
  refine ⟨10134787976328298433697467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6756525317552198955798311 10134787976328298433697467)
  ·
    refine ⟨15202181964492447650546201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10134787976328298433697467 15202181964492447650546201)
    ·
      refine ⟨11401636473369335737909651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15202181964492447650546201 11401636473369335737909651)
      ·
        refine ⟨17102454710054003606864477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11401636473369335737909651 17102454710054003606864477)
        ·
          refine ⟨6413420516270251352574179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17102454710054003606864477 6413420516270251352574179)
          ·
            refine ⟨9620130774405377028861269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6413420516270251352574179 9620130774405377028861269)
            ·
              refine ⟨14091988439070376507121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9620130774405377028861269 14091988439070376507121)
              ·
                rfl

theorem cell20_277871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 11].length) (baseStart_277871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277871 prefixEnd_277871 := by exact prefixLift 277871
  have htrace : WordTrace (prefixWord ++ tailWord_277871) baseStart_277871 baseEnd_277871 := by
    simpa [prefixWord, tailWord_277871, baseEnd_277871] using wordTrace_append hprefix tailTrace_277871
  have hstable : (prefixWord ++ tailWord_277871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277871).length < 2 ^ (prefixWord ++ tailWord_277871).sum := by decide
  have hdescent : baseEnd_277871 < baseStart_277871 := by decide
  rcases family_descends (prefixWord ++ tailWord_277871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277891 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 3]
def baseStart_277891 : Nat := 118140960795 + 277891 * 2 ^ 59
def prefixEnd_277891 : Nat := 4983230072969 + 3 ^ 40 * 277891 * 2
def baseEnd_277891 : Nat := 126837024496602207897341

theorem tailTrace_277891 : CollatzResearch.WordTrace tailWord_277891 prefixEnd_277891 126837024496602207897341 := by
  unfold tailWord_277891
  simp only [CollatzResearch.WordTrace]
  refine ⟨10135517436255841849425527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6757011624170561232950351 10135517436255841849425527)
  ·
    refine ⟨15203276154383762774138291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10135517436255841849425527 15203276154383762774138291)
    ·
      refine ⟨22804914231575644161207437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15203276154383762774138291 22804914231575644161207437)
      ·
        refine ⟨8551842836840866560452789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22804914231575644161207437 8551842836840866560452789)
        ·
          refine ⟨801735265953831240042449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8551842836840866560452789 801735265953831240042449)
          ·
            refine ⟨601301449465373430031837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 801735265953831240042449 601301449465373430031837)
            ·
              refine ⟨225488043549515036261939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 601301449465373430031837 225488043549515036261939)
              ·
                refine ⟨338232065324272554392909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225488043549515036261939 338232065324272554392909)
                ·
                  refine ⟨126837024496602207897341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338232065324272554392909 126837024496602207897341)
                  ·
                    rfl

theorem cell20_277891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 3].length) (baseStart_277891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277891 prefixEnd_277891 := by exact prefixLift 277891
  have htrace : WordTrace (prefixWord ++ tailWord_277891) baseStart_277891 baseEnd_277891 := by
    simpa [prefixWord, tailWord_277891, baseEnd_277891] using wordTrace_append hprefix tailTrace_277891
  have hstable : (prefixWord ++ tailWord_277891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277891).length < 2 ^ (prefixWord ++ tailWord_277891).sum := by decide
  have hdescent : baseEnd_277891 < baseStart_277891 := by decide
  rcases family_descends (prefixWord ++ tailWord_277891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277964 : List Nat := [2, 2, 1, 4, 2, 1, 2, 6]
def baseStart_277964 : Nat := 118140960795 + 277964 * 2 ^ 59
def prefixEnd_277964 : Nat := 4983230072969 + 3 ^ 40 * 277964 * 2
def baseEnd_277964 : Nat := 42290114561912799487903

theorem tailTrace_277964 : CollatzResearch.WordTrace tailWord_277964 prefixEnd_277964 42290114561912799487903 := by
  unfold tailWord_277964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069089982495687658416473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6758786643327583544555297 5069089982495687658416473)
  ·
    refine ⟨3801817486871765743812355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5069089982495687658416473 3801817486871765743812355)
    ·
      refine ⟨5702726230307648615718533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3801817486871765743812355 5702726230307648615718533)
      ·
        refine ⟨1069261168182684115447225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5702726230307648615718533 1069261168182684115447225)
        ·
          refine ⟨801945876137013086585419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069261168182684115447225 801945876137013086585419)
          ·
            refine ⟨1202918814205519629878129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801945876137013086585419 1202918814205519629878129)
            ·
              refine ⟨902189110654139722408597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202918814205519629878129 902189110654139722408597)
              ·
                refine ⟨42290114561912799487903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 902189110654139722408597 42290114561912799487903)
                ·
                  rfl

theorem cell20_277964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_277964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277964 prefixEnd_277964 := by exact prefixLift 277964
  have htrace : WordTrace (prefixWord ++ tailWord_277964) baseStart_277964 baseEnd_277964 := by
    simpa [prefixWord, tailWord_277964, baseEnd_277964] using wordTrace_append hprefix tailTrace_277964
  have hstable : (prefixWord ++ tailWord_277964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277964).length < 2 ^ (prefixWord ++ tailWord_277964).sum := by decide
  have hdescent : baseEnd_277964 < baseStart_277964 := by decide
  rcases family_descends (prefixWord ++ tailWord_277964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277985 : List Nat := [1, 2, 3, 1, 2, 11]
def baseStart_277985 : Nat := 118140960795 + 277985 * 2 ^ 59
def prefixEnd_277985 : Nat := 4983230072969 + 3 ^ 40 * 277985 * 2
def baseEnd_277985 : Nat := 4699256616961320694949

theorem tailTrace_277985 : CollatzResearch.WordTrace tailWord_277985 prefixEnd_277985 4699256616961320694949 := by
  unfold tailWord_277985
  simp only [CollatzResearch.WordTrace]
  refine ⟨10138945897915295903347409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6759297265276863935564939 10138945897915295903347409)
  ·
    refine ⟨7604209423436471927510557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10138945897915295903347409 7604209423436471927510557)
    ·
      refine ⟨2851578533788676972816459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7604209423436471927510557 2851578533788676972816459)
      ·
        refine ⟨4277367800683015459224689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851578533788676972816459 4277367800683015459224689)
        ·
          refine ⟨3208025850512261594418517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4277367800683015459224689 3208025850512261594418517)
          ·
            refine ⟨4699256616961320694949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3208025850512261594418517 4699256616961320694949)
            ·
              rfl

theorem cell20_277985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 11].length) (baseStart_277985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277985 prefixEnd_277985 := by exact prefixLift 277985
  have htrace : WordTrace (prefixWord ++ tailWord_277985) baseStart_277985 baseEnd_277985 := by
    simpa [prefixWord, tailWord_277985, baseEnd_277985] using wordTrace_append hprefix tailTrace_277985
  have hstable : (prefixWord ++ tailWord_277985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277985).length < 2 ^ (prefixWord ++ tailWord_277985).sum := by decide
  have hdescent : baseEnd_277985 < baseStart_277985 := by decide
  rcases family_descends (prefixWord ++ tailWord_277985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277991 : List Nat := [1, 1, 5, 2, 1, 2, 4, 2, 2]
def baseStart_277991 : Nat := 118140960795 + 277991 * 2 ^ 59
def prefixEnd_277991 : Nat := 4983230072969 + 3 ^ 40 * 277991 * 2
def baseEnd_277991 : Nat := 126882667221446304563599

theorem tailTrace_277991 : CollatzResearch.WordTrace tailWord_277991 prefixEnd_277991 126882667221446304563599 := by
  unfold tailWord_277991
  simp only [CollatzResearch.WordTrace]
  refine ⟨10139164735893558928065827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6759443157262372618710551 10139164735893558928065827)
  ·
    refine ⟨15208747103840338392098741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10139164735893558928065827 15208747103840338392098741)
    ·
      refine ⟨1425820040985031724259257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15208747103840338392098741 1425820040985031724259257)
      ·
        refine ⟨1069365030738773793194443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1425820040985031724259257 1069365030738773793194443)
        ·
          refine ⟨1604047546108160689791665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069365030738773793194443 1604047546108160689791665)
          ·
            refine ⟨1203035659581120517343749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1604047546108160689791665 1203035659581120517343749)
            ·
              refine ⟨225569186171460097001953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1203035659581120517343749 225569186171460097001953)
              ·
                refine ⟨169176889628595072751465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225569186171460097001953 169176889628595072751465)
                ·
                  refine ⟨126882667221446304563599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169176889628595072751465 126882667221446304563599)
                  ·
                    rfl

theorem cell20_277991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 2].length) (baseStart_277991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_277991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_277991 prefixEnd_277991 := by exact prefixLift 277991
  have htrace : WordTrace (prefixWord ++ tailWord_277991) baseStart_277991 baseEnd_277991 := by
    simpa [prefixWord, tailWord_277991, baseEnd_277991] using wordTrace_append hprefix tailTrace_277991
  have hstable : (prefixWord ++ tailWord_277991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277991).length < 2 ^ (prefixWord ++ tailWord_277991).sum := by decide
  have hdescent : baseEnd_277991 < baseStart_277991 := by decide
  rcases family_descends (prefixWord ++ tailWord_277991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278005 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 3]
def baseStart_278005 : Nat := 118140960795 + 278005 * 2 ^ 59
def prefixEnd_278005 : Nat := 4983230072969 + 3 ^ 40 * 278005 * 2
def baseEnd_278005 : Nat := 126889057202924478096875

theorem tailTrace_278005 : CollatzResearch.WordTrace tailWord_278005 prefixEnd_278005 126889057202924478096875 := by
  unfold tailWord_278005
  simp only [CollatzResearch.WordTrace]
  refine ⟨10139675357842839319075469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6759783571895226212716979 10139675357842839319075469)
  ·
    refine ⟨3802378259191064744653301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10139675357842839319075469 3802378259191064744653301)
    ·
      refine ⟨356472961799162319811247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3802378259191064744653301 356472961799162319811247)
      ·
        refine ⟨534709442698743479716871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356472961799162319811247 534709442698743479716871)
        ·
          refine ⟨802064164048115219575307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534709442698743479716871 802064164048115219575307)
          ·
            refine ⟨1203096246072172829362961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802064164048115219575307 1203096246072172829362961)
            ·
              refine ⟨902322184554129622022221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203096246072172829362961 902322184554129622022221)
              ·
                refine ⟨338370819207798608258333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902322184554129622022221 338370819207798608258333)
                ·
                  refine ⟨126889057202924478096875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338370819207798608258333 126889057202924478096875)
                  ·
                    rfl

theorem cell20_278005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_278005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278005 prefixEnd_278005 := by exact prefixLift 278005
  have htrace : WordTrace (prefixWord ++ tailWord_278005) baseStart_278005 baseEnd_278005 := by
    simpa [prefixWord, tailWord_278005, baseEnd_278005] using wordTrace_append hprefix tailTrace_278005
  have hstable : (prefixWord ++ tailWord_278005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278005).length < 2 ^ (prefixWord ++ tailWord_278005).sum := by decide
  have hdescent : baseEnd_278005 < baseStart_278005 := by decide
  rcases family_descends (prefixWord ++ tailWord_278005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278040 : List Nat := [2, 1, 2, 3, 4, 1, 7]
def baseStart_278040 : Nat := 118140960795 + 278040 * 2 ^ 59
def prefixEnd_278040 : Nat := 4983230072969 + 3 ^ 40 * 278040 * 2
def baseEnd_278040 : Nat := 14100559128513323547785

theorem tailTrace_278040 : CollatzResearch.WordTrace tailWord_278040 prefixEnd_278040 14100559128513323547785 := by
  unfold tailWord_278040
  simp only [CollatzResearch.WordTrace]
  refine ⟨5070475956358020148299787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6760634608477360197733049 5070475956358020148299787)
  ·
    refine ⟨7605713934537030222449681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5070475956358020148299787 7605713934537030222449681)
    ·
      refine ⟨5704285450902772666837261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7605713934537030222449681 5704285450902772666837261)
      ·
        refine ⟨2139107044088539750063973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5704285450902772666837261 2139107044088539750063973)
        ·
          refine ⟨401082570766601203136995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2139107044088539750063973 401082570766601203136995)
          ·
            refine ⟨601623856149901804705493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401082570766601203136995 601623856149901804705493)
            ·
              refine ⟨14100559128513323547785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 601623856149901804705493 14100559128513323547785)
              ·
                rfl

theorem cell20_278040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 7].length) (baseStart_278040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278040 prefixEnd_278040 := by exact prefixLift 278040
  have htrace : WordTrace (prefixWord ++ tailWord_278040) baseStart_278040 baseEnd_278040 := by
    simpa [prefixWord, tailWord_278040, baseEnd_278040] using wordTrace_append hprefix tailTrace_278040
  have hstable : (prefixWord ++ tailWord_278040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278040).length < 2 ^ (prefixWord ++ tailWord_278040).sum := by decide
  have hdescent : baseEnd_278040 < baseStart_278040 := by decide
  rcases family_descends (prefixWord ++ tailWord_278040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278050 : List Nat := [3, 3, 1, 1, 1, 1, 4, 4, 2]
def baseStart_278050 : Nat := 118140960795 + 278050 * 2 ^ 59
def prefixEnd_278050 : Nat := 4983230072969 + 3 ^ 40 * 278050 * 2
def baseEnd_278050 : Nat := 126909596429104321596691

theorem tailTrace_278050 : CollatzResearch.WordTrace tailWord_278050 prefixEnd_278050 126909596429104321596691 := by
  unfold tailWord_278050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535329160669953001115901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6760877761786541336309069 2535329160669953001115901)
  ·
    refine ⟨950748435251232375418463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2535329160669953001115901 950748435251232375418463)
    ·
      refine ⟨1426122652876848563127695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950748435251232375418463 1426122652876848563127695)
      ·
        refine ⟨2139183979315272844691543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426122652876848563127695 2139183979315272844691543)
        ·
          refine ⟨3208775968972909267037315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139183979315272844691543 3208775968972909267037315)
          ·
            refine ⟨4813163953459363900555973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3208775968972909267037315 4813163953459363900555973)
            ·
              refine ⟨902468241273630731354245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4813163953459363900555973 902468241273630731354245)
              ·
                refine ⟨169212795238805762128921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 902468241273630731354245 169212795238805762128921)
                ·
                  refine ⟨126909596429104321596691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169212795238805762128921 126909596429104321596691)
                  ·
                    rfl

theorem cell20_278050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_278050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278050 prefixEnd_278050 := by exact prefixLift 278050
  have htrace : WordTrace (prefixWord ++ tailWord_278050) baseStart_278050 baseEnd_278050 := by
    simpa [prefixWord, tailWord_278050, baseEnd_278050] using wordTrace_append hprefix tailTrace_278050
  have hstable : (prefixWord ++ tailWord_278050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278050).length < 2 ^ (prefixWord ++ tailWord_278050).sum := by decide
  have hdescent : baseEnd_278050 < baseStart_278050 := by decide
  rcases family_descends (prefixWord ++ tailWord_278050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278116 : List Nat := [2, 3, 1, 1, 2, 4, 2, 5]
def baseStart_278116 : Nat := 118140960795 + 278116 * 2 ^ 59
def prefixEnd_278116 : Nat := 4983230072969 + 3 ^ 40 * 278116 * 2
def baseEnd_278116 : Nat := 42313240209167141798807

theorem tailTrace_278116 : CollatzResearch.WordTrace tailWord_278116 prefixEnd_278116 42313240209167141798807 := by
  unfold tailWord_278116
  simp only [CollatzResearch.WordTrace]
  refine ⟨5071861930220352638183101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6762482573627136850910801 5071861930220352638183101)
  ·
    refine ⟨1901948223832632239318663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5071861930220352638183101 1901948223832632239318663)
    ·
      refine ⟨2852922335748948358977995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1901948223832632239318663 2852922335748948358977995)
      ·
        refine ⟨4279383503623422538466993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852922335748948358977995 4279383503623422538466993)
        ·
          refine ⟨3209537627717566903850245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4279383503623422538466993 3209537627717566903850245)
          ·
            refine ⟨601788305197043794471921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3209537627717566903850245 601788305197043794471921)
            ·
              refine ⟨451341228897782845853941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601788305197043794471921 451341228897782845853941)
              ·
                refine ⟨42313240209167141798807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 451341228897782845853941 42313240209167141798807)
                ·
                  rfl

theorem cell20_278116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_278116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278116 prefixEnd_278116 := by exact prefixLift 278116
  have htrace : WordTrace (prefixWord ++ tailWord_278116) baseStart_278116 baseEnd_278116 := by
    simpa [prefixWord, tailWord_278116, baseEnd_278116] using wordTrace_append hprefix tailTrace_278116
  have hstable : (prefixWord ++ tailWord_278116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278116).length < 2 ^ (prefixWord ++ tailWord_278116).sum := by decide
  have hdescent : baseEnd_278116 < baseStart_278116 := by decide
  rcases family_descends (prefixWord ++ tailWord_278116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278137 : List Nat := [1, 2, 1, 3, 3, 1, 1, 8]
def baseStart_278137 : Nat := 118140960795 + 278137 * 2 ^ 59
def prefixEnd_278137 : Nat := 4983230072969 + 3 ^ 40 * 278137 * 2
def baseEnd_278137 : Nat := 42316435199906228565445

theorem tailTrace_278137 : CollatzResearch.WordTrace tailWord_278137 prefixEnd_278137 42316435199906228565445 := by
  unfold tailWord_278137
  simp only [CollatzResearch.WordTrace]
  refine ⟨10144489793364625862880665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6762993195576417241920443 10144489793364625862880665)
  ·
    refine ⟨7608367345023469397160499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10144489793364625862880665 7608367345023469397160499)
    ·
      refine ⟨11412551017535204095740749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7608367345023469397160499 11412551017535204095740749)
      ·
        refine ⟨4279706631575701535902781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11412551017535204095740749 4279706631575701535902781)
        ·
          refine ⟨1604889986840888075963543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4279706631575701535902781 1604889986840888075963543)
          ·
            refine ⟨2407334980261332113945315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1604889986840888075963543 2407334980261332113945315)
            ·
              refine ⟨3611002470391998170917973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2407334980261332113945315 3611002470391998170917973)
              ·
                refine ⟨42316435199906228565445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3611002470391998170917973 42316435199906228565445)
                ·
                  rfl

theorem cell20_278137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_278137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278137 prefixEnd_278137 := by exact prefixLift 278137
  have htrace : WordTrace (prefixWord ++ tailWord_278137) baseStart_278137 baseEnd_278137 := by
    simpa [prefixWord, tailWord_278137, baseEnd_278137] using wordTrace_append hprefix tailTrace_278137
  have hstable : (prefixWord ++ tailWord_278137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278137).length < 2 ^ (prefixWord ++ tailWord_278137).sum := by decide
  have hdescent : baseEnd_278137 < baseStart_278137 := by decide
  rcases family_descends (prefixWord ++ tailWord_278137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278147 : List Nat := [1, 1, 1, 3, 3, 1, 1, 7, 2]
def baseStart_278147 : Nat := 118140960795 + 278147 * 2 ^ 59
def prefixEnd_278147 : Nat := 4983230072969 + 3 ^ 40 * 278147 * 2
def baseEnd_278147 : Nat := 126953869872203095362961

theorem tailTrace_278147 : CollatzResearch.WordTrace tailWord_278147 prefixEnd_278147 126953869872203095362961 := by
  unfold tailWord_278147
  simp only [CollatzResearch.WordTrace]
  refine ⟨10144854523328397570744695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6763236348885598380496463 10144854523328397570744695)
  ·
    refine ⟨15217281784992596356117043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10144854523328397570744695 15217281784992596356117043)
    ·
      refine ⟨22825922677488894534175565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15217281784992596356117043 22825922677488894534175565)
      ·
        refine ⟨8559721004058335450315837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22825922677488894534175565 8559721004058335450315837)
        ·
          refine ⟨3209895376521875793868439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8559721004058335450315837 3209895376521875793868439)
          ·
            refine ⟨4814843064782813690802659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209895376521875793868439 4814843064782813690802659)
            ·
              refine ⟨7222264597174220536203989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814843064782813690802659 7222264597174220536203989)
              ·
                refine ⟨169271826496270793817281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7222264597174220536203989 169271826496270793817281)
                ·
                  refine ⟨126953869872203095362961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169271826496270793817281 126953869872203095362961)
                  ·
                    rfl

theorem cell20_278147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 2].length) (baseStart_278147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278147 prefixEnd_278147 := by exact prefixLift 278147
  have htrace : WordTrace (prefixWord ++ tailWord_278147) baseStart_278147 baseEnd_278147 := by
    simpa [prefixWord, tailWord_278147, baseEnd_278147] using wordTrace_append hprefix tailTrace_278147
  have hstable : (prefixWord ++ tailWord_278147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278147).length < 2 ^ (prefixWord ++ tailWord_278147).sum := by decide
  have hdescent : baseEnd_278147 < baseStart_278147 := by decide
  rcases family_descends (prefixWord ++ tailWord_278147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278198 : List Nat := [5, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_278198 : Nat := 118140960795 + 278198 * 2 ^ 59
def prefixEnd_278198 : Nat := 4983230072969 + 3 ^ 40 * 278198 * 2
def baseEnd_278198 : Nat := 126977147661873584662753

theorem tailTrace_278198 : CollatzResearch.WordTrace tailWord_278198 prefixEnd_278198 126977147661873584662753 := by
  unfold tailWord_278198
  simp only [CollatzResearch.WordTrace]
  refine ⟨634169665383977080053203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6764476430762422187234165 634169665383977080053203)
  ·
    refine ⟨951254498075965620079805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 634169665383977080053203 951254498075965620079805)
    ·
      refine ⟨356720436778487107529927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 951254498075965620079805 356720436778487107529927)
      ·
        refine ⟨535080655167730661294891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356720436778487107529927 535080655167730661294891)
        ·
          refine ⟨802620982751595991942337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535080655167730661294891 802620982751595991942337)
          ·
            refine ⟨601965737063696993956753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802620982751595991942337 601965737063696993956753)
            ·
              refine ⟨451474302797772745467565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601965737063696993956753 451474302797772745467565)
              ·
                refine ⟨169302863549164779550337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 451474302797772745467565 169302863549164779550337)
                ·
                  refine ⟨126977147661873584662753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169302863549164779550337 126977147661873584662753)
                  ·
                    rfl

theorem cell20_278198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_278198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278198 prefixEnd_278198 := by exact prefixLift 278198
  have htrace : WordTrace (prefixWord ++ tailWord_278198) baseStart_278198 baseEnd_278198 := by
    simpa [prefixWord, tailWord_278198, baseEnd_278198] using wordTrace_append hprefix tailTrace_278198
  have hstable : (prefixWord ++ tailWord_278198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278198).length < 2 ^ (prefixWord ++ tailWord_278198).sum := by decide
  have hdescent : baseEnd_278198 < baseStart_278198 := by decide
  rcases family_descends (prefixWord ++ tailWord_278198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278202 : List Nat := [3, 1, 1, 1, 2, 5, 2, 3, 2]
def baseStart_278202 : Nat := 118140960795 + 278202 * 2 ^ 59
def prefixEnd_278202 : Nat := 4983230072969 + 3 ^ 40 * 278202 * 2
def baseEnd_278202 : Nat := 126978973370867348529403

theorem tailTrace_278202 : CollatzResearch.WordTrace tailWord_278202 prefixEnd_278202 126978973370867348529403 := by
  unfold tailWord_278202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536715134532285490999215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6764573692086094642664573 2536715134532285490999215)
  ·
    refine ⟨3805072701798428236498823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2536715134532285490999215 3805072701798428236498823)
    ·
      refine ⟨5707609052697642354748235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3805072701798428236498823 5707609052697642354748235)
      ·
        refine ⟨8561413579046463532122353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5707609052697642354748235 8561413579046463532122353)
        ·
          refine ⟨6421060184284847649091765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8561413579046463532122353 6421060184284847649091765)
          ·
            refine ⟨601974392276704467102353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6421060184284847649091765 601974392276704467102353)
            ·
              refine ⟨451480794207528350326765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601974392276704467102353 451480794207528350326765)
              ·
                refine ⟨169305297827823131372537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 451480794207528350326765 169305297827823131372537)
                ·
                  refine ⟨126978973370867348529403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169305297827823131372537 126978973370867348529403)
                  ·
                    rfl

theorem cell20_278202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_278202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278202 prefixEnd_278202 := by exact prefixLift 278202
  have htrace : WordTrace (prefixWord ++ tailWord_278202) baseStart_278202 baseEnd_278202 := by
    simpa [prefixWord, tailWord_278202, baseEnd_278202] using wordTrace_append hprefix tailTrace_278202
  have hstable : (prefixWord ++ tailWord_278202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278202).length < 2 ^ (prefixWord ++ tailWord_278202).sum := by decide
  have hdescent : baseEnd_278202 < baseStart_278202 := by decide
  rcases family_descends (prefixWord ++ tailWord_278202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278244 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_278244 : Nat := 118140960795 + 278244 * 2 ^ 59
def prefixEnd_278244 : Nat := 4983230072969 + 3 ^ 40 * 278244 * 2
def baseEnd_278244 : Nat := 126998143315301869129231

theorem tailTrace_278244 : CollatzResearch.WordTrace tailWord_278244 prefixEnd_278244 126998143315301869129231 := by
  unfold tailWord_278244
  simp only [CollatzResearch.WordTrace]
  refine ⟨5074196201988491568512893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6765594935984655424683857 5074196201988491568512893)
  ·
    refine ⟨1902823575745684338192335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5074196201988491568512893 1902823575745684338192335)
    ·
      refine ⟨2854235363618526507288503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902823575745684338192335 2854235363618526507288503)
      ·
        refine ⟨4281353045427789760932755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2854235363618526507288503 4281353045427789760932755)
        ·
          refine ⟨6422029568141684641399133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4281353045427789760932755 6422029568141684641399133)
          ·
            refine ⟨2408261088053131740524675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6422029568141684641399133 2408261088053131740524675)
            ·
              refine ⟨3612391632079697610787013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408261088053131740524675 3612391632079697610787013)
              ·
                refine ⟨677323431014943302022565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3612391632079697610787013 677323431014943302022565)
                ·
                  refine ⟨126998143315301869129231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 677323431014943302022565 126998143315301869129231)
                  ·
                    rfl

theorem cell20_278244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_278244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278244 prefixEnd_278244 := by exact prefixLift 278244
  have htrace : WordTrace (prefixWord ++ tailWord_278244) baseStart_278244 baseEnd_278244 := by
    simpa [prefixWord, tailWord_278244, baseEnd_278244] using wordTrace_append hprefix tailTrace_278244
  have hstable : (prefixWord ++ tailWord_278244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278244).length < 2 ^ (prefixWord ++ tailWord_278244).sum := by decide
  have hdescent : baseEnd_278244 < baseStart_278244 := by decide
  rcases family_descends (prefixWord ++ tailWord_278244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278247 : List Nat := [1, 1, 5, 4, 1, 1, 1, 6]
def baseStart_278247 : Nat := 118140960795 + 278247 * 2 ^ 59
def prefixEnd_278247 : Nat := 4983230072969 + 3 ^ 40 * 278247 * 2
def baseEnd_278247 : Nat := 42333170865682397343073

theorem tailTrace_278247 : CollatzResearch.WordTrace tailWord_278247 prefixEnd_278247 42333170865682397343073 := by
  unfold tailWord_278247
  simp only [CollatzResearch.WordTrace]
  refine ⟨10148501822966114649384995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6765667881977409766256663 10148501822966114649384995)
  ·
    refine ⟨15222752734449171974077493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10148501822966114649384995 15222752734449171974077493)
    ·
      refine ⟨1427133068854609872569765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15222752734449171974077493 1427133068854609872569765)
      ·
        refine ⟨267587450410239351106831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1427133068854609872569765 267587450410239351106831)
        ·
          refine ⟨401381175615359026660247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267587450410239351106831 401381175615359026660247)
          ·
            refine ⟨602071763423038539990371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401381175615359026660247 602071763423038539990371)
            ·
              refine ⟨903107645134557809985557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602071763423038539990371 903107645134557809985557)
              ·
                refine ⟨42333170865682397343073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 903107645134557809985557 42333170865682397343073)
                ·
                  rfl

theorem cell20_278247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 6].length) (baseStart_278247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278247 prefixEnd_278247 := by exact prefixLift 278247
  have htrace : WordTrace (prefixWord ++ tailWord_278247) baseStart_278247 baseEnd_278247 := by
    simpa [prefixWord, tailWord_278247, baseEnd_278247] using wordTrace_append hprefix tailTrace_278247
  have hstable : (prefixWord ++ tailWord_278247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278247).length < 2 ^ (prefixWord ++ tailWord_278247).sum := by decide
  have hdescent : baseEnd_278247 < baseStart_278247 := by decide
  rcases family_descends (prefixWord ++ tailWord_278247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278329 : List Nat := [1, 2, 1, 7, 2, 1, 2, 2, 2]
def baseStart_278329 : Nat := 118140960795 + 278329 * 2 ^ 59
def prefixEnd_278329 : Nat := 4983230072969 + 3 ^ 40 * 278329 * 2
def baseEnd_278329 : Nat := 127036939631419351295551

theorem tailTrace_278329 : CollatzResearch.WordTrace tailWord_278329 prefixEnd_278329 127036939631419351295551 := by
  unfold tailWord_278329
  simp only [CollatzResearch.WordTrace]
  refine ⟨10151492608669042653870041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6767661739112695102580027 10151492608669042653870041)
  ·
    refine ⟨7613619456501781990402531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10151492608669042653870041 7613619456501781990402531)
    ·
      refine ⟨11420429184752672985603797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7613619456501781990402531 11420429184752672985603797)
      ·
        refine ⟨267666309017640773100089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 11420429184752672985603797 267666309017640773100089)
        ·
          refine ⟨200749731763230579825067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267666309017640773100089 200749731763230579825067)
          ·
            refine ⟨301124597644845869737601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200749731763230579825067 301124597644845869737601)
            ·
              refine ⟨225843448233634402303201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301124597644845869737601 225843448233634402303201)
              ·
                refine ⟨169382586175225801727401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225843448233634402303201 169382586175225801727401)
                ·
                  refine ⟨127036939631419351295551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169382586175225801727401 127036939631419351295551)
                  ·
                    rfl

theorem cell20_278329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_278329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278329 prefixEnd_278329 := by exact prefixLift 278329
  have htrace : WordTrace (prefixWord ++ tailWord_278329) baseStart_278329 baseEnd_278329 := by
    simpa [prefixWord, tailWord_278329, baseEnd_278329] using wordTrace_append hprefix tailTrace_278329
  have hstable : (prefixWord ++ tailWord_278329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278329).length < 2 ^ (prefixWord ++ tailWord_278329).sum := by decide
  have hdescent : baseEnd_278329 < baseStart_278329 := by decide
  rcases family_descends (prefixWord ++ tailWord_278329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278330 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_278330 : Nat := 118140960795 + 278330 * 2 ^ 59
def prefixEnd_278330 : Nat := 4983230072969 + 3 ^ 40 * 278330 * 2
def baseEnd_278330 : Nat := 127037396058667792262213

theorem tailTrace_278330 : CollatzResearch.WordTrace tailWord_278330 prefixEnd_278330 127037396058667792262213 := by
  unfold tailWord_278330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2537882270416354956164111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6767686054443613216437629 2537882270416354956164111)
  ·
    refine ⟨3806823405624532434246167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2537882270416354956164111 3806823405624532434246167)
    ·
      refine ⟨5710235108436798651369251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3806823405624532434246167 5710235108436798651369251)
      ·
        refine ⟨8565352662655197977053877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5710235108436798651369251 8565352662655197977053877)
        ·
          refine ⟨803001812123924810348801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8565352662655197977053877 803001812123924810348801)
          ·
            refine ⟨602251359092943607761601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 803001812123924810348801 602251359092943607761601)
            ·
              refine ⟨451688519319707705821201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602251359092943607761601 451688519319707705821201)
              ·
                refine ⟨338766389489780779365901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451688519319707705821201 338766389489780779365901)
                ·
                  refine ⟨127037396058667792262213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338766389489780779365901 127037396058667792262213)
                  ·
                    rfl

theorem cell20_278330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_278330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278330 prefixEnd_278330 := by exact prefixLift 278330
  have htrace : WordTrace (prefixWord ++ tailWord_278330) baseStart_278330 baseEnd_278330 := by
    simpa [prefixWord, tailWord_278330, baseEnd_278330] using wordTrace_append hprefix tailTrace_278330
  have hstable : (prefixWord ++ tailWord_278330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278330).length < 2 ^ (prefixWord ++ tailWord_278330).sum := by decide
  have hdescent : baseEnd_278330 < baseStart_278330 := by decide
  rcases family_descends (prefixWord ++ tailWord_278330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278333 : List Nat := [1, 4, 1, 4, 1, 1, 4, 2, 2]
def baseStart_278333 : Nat := 118140960795 + 278333 * 2 ^ 59
def prefixEnd_278333 : Nat := 4983230072969 + 3 ^ 40 * 278333 * 2
def baseEnd_278333 : Nat := 127038765340413115162201

theorem tailTrace_278333 : CollatzResearch.WordTrace tailWord_278333 prefixEnd_278333 127038765340413115162201 := by
  unfold tailWord_278333
  simp only [CollatzResearch.WordTrace]
  refine ⟨10151638500654551337015653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6767759000436367558010435 10151638500654551337015653)
  ·
    refine ⟨1903432218872728375690435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10151638500654551337015653 1903432218872728375690435)
    ·
      refine ⟨2855148328309092563535653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903432218872728375690435 2855148328309092563535653)
      ·
        refine ⟨535340311557954855662935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2855148328309092563535653 535340311557954855662935)
        ·
          refine ⟨803010467336932283494403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535340311557954855662935 803010467336932283494403)
          ·
            refine ⟨1204515701005398425241605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803010467336932283494403 1204515701005398425241605)
            ·
              refine ⟨225846693938512204732801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1204515701005398425241605 225846693938512204732801)
              ·
                refine ⟨169385020453884153549601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225846693938512204732801 169385020453884153549601)
                ·
                  refine ⟨127038765340413115162201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169385020453884153549601 127038765340413115162201)
                  ·
                    rfl

theorem cell20_278333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_278333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278333 prefixEnd_278333 := by exact prefixLift 278333
  have htrace : WordTrace (prefixWord ++ tailWord_278333) baseStart_278333 baseEnd_278333 := by
    simpa [prefixWord, tailWord_278333, baseEnd_278333] using wordTrace_append hprefix tailTrace_278333
  have hstable : (prefixWord ++ tailWord_278333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278333).length < 2 ^ (prefixWord ++ tailWord_278333).sum := by decide
  have hdescent : baseEnd_278333 < baseStart_278333 := by decide
  rcases family_descends (prefixWord ++ tailWord_278333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278344 : List Nat := [2, 1, 3, 1, 1, 6, 1, 5]
def baseStart_278344 : Nat := 118140960795 + 278344 * 2 ^ 59
def prefixEnd_278344 : Nat := 4983230072969 + 3 ^ 40 * 278344 * 2
def baseEnd_278344 : Nat := 42347928680048655265163

theorem tailTrace_278344 : CollatzResearch.WordTrace tailWord_278344 prefixEnd_278344 42347928680048655265163 := by
  unfold tailWord_278344
  simp only [CollatzResearch.WordTrace]
  refine ⟨5076019851807350107833043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6768026469076466810444057 5076019851807350107833043)
  ·
    refine ⟨7614029777711025161749565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5076019851807350107833043 7614029777711025161749565)
    ·
      refine ⟨2855261166641634435656087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7614029777711025161749565 2855261166641634435656087)
      ·
        refine ⟨4282891749962451653484131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2855261166641634435656087 4282891749962451653484131)
        ·
          refine ⟨6424337624943677480226197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282891749962451653484131 6424337624943677480226197)
          ·
            refine ⟨301140826169234881885603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6424337624943677480226197 301140826169234881885603)
            ·
              refine ⟨451711239253852322828405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301140826169234881885603 451711239253852322828405)
              ·
                refine ⟨42347928680048655265163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 451711239253852322828405 42347928680048655265163)
                ·
                  rfl

theorem cell20_278344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_278344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278344 prefixEnd_278344 := by exact prefixLift 278344
  have htrace : WordTrace (prefixWord ++ tailWord_278344) baseStart_278344 baseEnd_278344 := by
    simpa [prefixWord, tailWord_278344, baseEnd_278344] using wordTrace_append hprefix tailTrace_278344
  have hstable : (prefixWord ++ tailWord_278344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278344).length < 2 ^ (prefixWord ++ tailWord_278344).sum := by decide
  have hdescent : baseEnd_278344 < baseStart_278344 := by decide
  rcases family_descends (prefixWord ++ tailWord_278344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278379 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_278379 : Nat := 118140960795 + 278379 * 2 ^ 59
def prefixEnd_278379 : Nat := 4983230072969 + 3 ^ 40 * 278379 * 2
def baseEnd_278379 : Nat := 127059760993841399628679

theorem tailTrace_278379 : CollatzResearch.WordTrace tailWord_278379 prefixEnd_278379 127059760993841399628679 := by
  unfold tailWord_278379
  simp only [CollatzResearch.WordTrace]
  refine ⟨10153316258487901193190191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6768877505658600795460127 10153316258487901193190191)
  ·
    refine ⟨15229974387731851789785287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10153316258487901193190191 15229974387731851789785287)
    ·
      refine ⟨22844961581597777684677931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15229974387731851789785287 22844961581597777684677931)
      ·
        refine ⟨34267442372396666527016897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22844961581597777684677931 34267442372396666527016897)
        ·
          refine ⟨25700581779297499895262673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34267442372396666527016897 25700581779297499895262673)
          ·
            refine ⟨19275436334473124921447005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25700581779297499895262673 19275436334473124921447005)
            ·
              refine ⟨7228288625427421845542627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19275436334473124921447005 7228288625427421845542627)
              ·
                refine ⟨10842432938141132768313941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7228288625427421845542627 10842432938141132768313941)
                ·
                  refine ⟨127059760993841399628679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10842432938141132768313941 127059760993841399628679)
                  ·
                    rfl

theorem cell20_278379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_278379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278379 prefixEnd_278379 := by exact prefixLift 278379
  have htrace : WordTrace (prefixWord ++ tailWord_278379) baseStart_278379 baseEnd_278379 := by
    simpa [prefixWord, tailWord_278379, baseEnd_278379] using wordTrace_append hprefix tailTrace_278379
  have hstable : (prefixWord ++ tailWord_278379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278379).length < 2 ^ (prefixWord ++ tailWord_278379).sum := by decide
  have hdescent : baseEnd_278379 < baseStart_278379 := by decide
  rcases family_descends (prefixWord ++ tailWord_278379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278382 : List Nat := [4, 1, 2, 3, 1, 2, 7]
def baseStart_278382 : Nat := 118140960795 + 278382 * 2 ^ 59
def prefixEnd_278382 : Nat := 4983230072969 + 3 ^ 40 * 278382 * 2
def baseEnd_278382 : Nat := 14117903363954080280963

theorem tailTrace_278382 : CollatzResearch.WordTrace tailWord_278382 prefixEnd_278382 14117903363954080280963 := by
  unfold tailWord_278382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1269178209684629088193675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6768950451651355137032933 1269178209684629088193675)
  ·
    refine ⟨1903767314526943632290513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1269178209684629088193675 1903767314526943632290513)
    ·
      refine ⟨1427825485895207724217885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1903767314526943632290513 1427825485895207724217885)
      ·
        refine ⟨535434557210702896581707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1427825485895207724217885 535434557210702896581707)
        ·
          refine ⟨803151835816054344872561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535434557210702896581707 803151835816054344872561)
          ·
            refine ⟨602363876862040758654421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 803151835816054344872561 602363876862040758654421)
            ·
              refine ⟨14117903363954080280963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 602363876862040758654421 14117903363954080280963)
              ·
                rfl

theorem cell20_278382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 7].length) (baseStart_278382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278382 prefixEnd_278382 := by exact prefixLift 278382
  have htrace : WordTrace (prefixWord ++ tailWord_278382) baseStart_278382 baseEnd_278382 := by
    simpa [prefixWord, tailWord_278382, baseEnd_278382] using wordTrace_append hprefix tailTrace_278382
  have hstable : (prefixWord ++ tailWord_278382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278382).length < 2 ^ (prefixWord ++ tailWord_278382).sum := by decide
  have hdescent : baseEnd_278382 < baseStart_278382 := by decide
  rcases family_descends (prefixWord ++ tailWord_278382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278389 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_278389 : Nat := 118140960795 + 278389 * 2 ^ 59
def prefixEnd_278389 : Nat := 4983230072969 + 3 ^ 40 * 278389 * 2
def baseEnd_278389 : Nat := 127064325266325809295305

theorem tailTrace_278389 : CollatzResearch.WordTrace tailWord_278389 prefixEnd_278389 127064325266325809295305 := by
  unfold tailWord_278389
  simp only [CollatzResearch.WordTrace]
  refine ⟨10153680988451672901054221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6769120658967781934036147 10153680988451672901054221)
  ·
    refine ⟨3807630370669377337895333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10153680988451672901054221 3807630370669377337895333)
    ·
      refine ⟨713930694500508250855375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3807630370669377337895333 713930694500508250855375)
      ·
        refine ⟨1070896041750762376283063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713930694500508250855375 1070896041750762376283063)
        ·
          refine ⟨1606344062626143564424595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070896041750762376283063 1606344062626143564424595)
          ·
            refine ⟨2409516093939215346636893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606344062626143564424595 2409516093939215346636893)
            ·
              refine ⟨903568535227205754988835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2409516093939215346636893 903568535227205754988835)
              ·
                refine ⟨1355352802840808632483253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903568535227205754988835 1355352802840808632483253)
                ·
                  refine ⟨127064325266325809295305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1355352802840808632483253 127064325266325809295305)
                  ·
                    rfl

theorem cell20_278389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_278389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278389 prefixEnd_278389 := by exact prefixLift 278389
  have htrace : WordTrace (prefixWord ++ tailWord_278389) baseStart_278389 baseEnd_278389 := by
    simpa [prefixWord, tailWord_278389, baseEnd_278389] using wordTrace_append hprefix tailTrace_278389
  have hstable : (prefixWord ++ tailWord_278389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278389).length < 2 ^ (prefixWord ++ tailWord_278389).sum := by decide
  have hdescent : baseEnd_278389 < baseStart_278389 := by decide
  rcases family_descends (prefixWord ++ tailWord_278389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278420 : List Nat := [2, 4, 2, 1, 1, 3, 1, 6]
def baseStart_278420 : Nat := 118140960795 + 278420 * 2 ^ 59
def prefixEnd_278420 : Nat := 4983230072969 + 3 ^ 40 * 278420 * 2
def baseEnd_278420 : Nat := 42359491503675826420615

theorem tailTrace_278420 : CollatzResearch.WordTrace tailWord_278420 prefixEnd_278420 42359491503675826420615 := by
  unfold tailWord_278420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5077405825669682597716357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6769874434226243463621809 5077405825669682597716357)
  ·
    refine ⟨952013592313065487071817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5077405825669682597716357 952013592313065487071817)
    ·
      refine ⟨714010194234799115303863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 952013592313065487071817 714010194234799115303863)
      ·
        refine ⟨1071015291352198672955795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 714010194234799115303863 1071015291352198672955795)
        ·
          refine ⟨1606522937028298009433693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071015291352198672955795 1606522937028298009433693)
          ·
            refine ⟨602446101385611753537635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1606522937028298009433693 602446101385611753537635)
            ·
              refine ⟨903669152078417630306453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602446101385611753537635 903669152078417630306453)
              ·
                refine ⟨42359491503675826420615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 903669152078417630306453 42359491503675826420615)
                ·
                  rfl

theorem cell20_278420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_278420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278420 prefixEnd_278420 := by exact prefixLift 278420
  have htrace : WordTrace (prefixWord ++ tailWord_278420) baseStart_278420 baseEnd_278420 := by
    simpa [prefixWord, tailWord_278420, baseEnd_278420] using wordTrace_append hprefix tailTrace_278420
  have hstable : (prefixWord ++ tailWord_278420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278420).length < 2 ^ (prefixWord ++ tailWord_278420).sum := by decide
  have hdescent : baseEnd_278420 < baseStart_278420 := by decide
  rcases family_descends (prefixWord ++ tailWord_278420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278422 : List Nat := [5, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_278422 : Nat := 118140960795 + 278422 * 2 ^ 59
def prefixEnd_278422 : Nat := 4983230072969 + 3 ^ 40 * 278422 * 2
def baseEnd_278422 : Nat := 127079387365524361195171

theorem tailTrace_278422 : CollatzResearch.WordTrace tailWord_278422 prefixEnd_278422 127079387365524361195171 := by
  unfold tailWord_278422
  simp only [CollatzResearch.WordTrace]
  refine ⟨634680287333257471062845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6769923064888079691337013 634680287333257471062845)
  ·
    refine ⟨238005107749971551648567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 634680287333257471062845 238005107749971551648567)
    ·
      refine ⟨357007661624957327472851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238005107749971551648567 357007661624957327472851)
      ·
        refine ⟨535511492437435991209277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357007661624957327472851 535511492437435991209277)
        ·
          refine ⟨200816809664038496703479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 535511492437435991209277 200816809664038496703479)
          ·
            refine ⟨301225214496057745055219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200816809664038496703479 301225214496057745055219)
            ·
              refine ⟨451837821744086617582829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301225214496057745055219 451837821744086617582829)
              ·
                refine ⟨169439183154032481593561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 451837821744086617582829 169439183154032481593561)
                ·
                  refine ⟨127079387365524361195171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169439183154032481593561 127079387365524361195171)
                  ·
                    rfl

theorem cell20_278422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_278422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278422 prefixEnd_278422 := by exact prefixLift 278422
  have htrace : WordTrace (prefixWord ++ tailWord_278422) baseStart_278422 baseEnd_278422 := by
    simpa [prefixWord, tailWord_278422, baseEnd_278422] using wordTrace_append hprefix tailTrace_278422
  have hstable : (prefixWord ++ tailWord_278422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278422).length < 2 ^ (prefixWord ++ tailWord_278422).sum := by decide
  have hdescent : baseEnd_278422 < baseStart_278422 := by decide
  rcases family_descends (prefixWord ++ tailWord_278422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278461 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 3]
def baseStart_278461 : Nat := 118140960795 + 278461 * 2 ^ 59
def prefixEnd_278461 : Nat := 4983230072969 + 3 ^ 40 * 278461 * 2
def baseEnd_278461 : Nat := 127097188028213558895011

theorem tailTrace_278461 : CollatzResearch.WordTrace tailWord_278461 prefixEnd_278461 127097188028213558895011 := by
  unfold tailWord_278461
  simp only [CollatzResearch.WordTrace]
  refine ⟨10156307044190829197675237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6770871362793886131783491 10156307044190829197675237)
  ·
    refine ⟨1904307570785780474564107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10156307044190829197675237 1904307570785780474564107)
    ·
      refine ⟨2856461356178670711846161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1904307570785780474564107 2856461356178670711846161)
      ·
        refine ⟨2142346017134003033884621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2856461356178670711846161 2142346017134003033884621)
        ·
          refine ⟨803379756425251137706733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2142346017134003033884621 803379756425251137706733)
          ·
            refine ⟨301267408659469176640025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 803379756425251137706733 301267408659469176640025)
            ·
              refine ⟨225950556494601882480019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301267408659469176640025 225950556494601882480019)
              ·
                refine ⟨338925834741902823720029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225950556494601882480019 338925834741902823720029)
                ·
                  refine ⟨127097188028213558895011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338925834741902823720029 127097188028213558895011)
                  ·
                    rfl

theorem cell20_278461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_278461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278461 prefixEnd_278461 := by exact prefixLift 278461
  have htrace : WordTrace (prefixWord ++ tailWord_278461) baseStart_278461 baseEnd_278461 := by
    simpa [prefixWord, tailWord_278461, baseEnd_278461] using wordTrace_append hprefix tailTrace_278461
  have hstable : (prefixWord ++ tailWord_278461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278461).length < 2 ^ (prefixWord ++ tailWord_278461).sum := by decide
  have hdescent : baseEnd_278461 < baseStart_278461 := by decide
  rcases family_descends (prefixWord ++ tailWord_278461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278492 : List Nat := [2, 2, 6, 1, 2, 7]
def baseStart_278492 : Nat := 118140960795 + 278492 * 2 ^ 59
def prefixEnd_278492 : Nat := 4983230072969 + 3 ^ 40 * 278492 * 2
def baseEnd_278492 : Nat := 4707827306404267735613

theorem tailTrace_278492 : CollatzResearch.WordTrace tailWord_278492 prefixEnd_278492 4707827306404267735613 := by
  unfold tailWord_278492
  simp only [CollatzResearch.WordTrace]
  refine ⟨5078718853539260746026865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6771625138052347661369153 5078718853539260746026865)
  ·
    refine ⟨3809039140154445559520149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5078718853539260746026865 3809039140154445559520149)
    ·
      refine ⟨178548709694739635602507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3809039140154445559520149 178548709694739635602507)
      ·
        refine ⟨267823064542109453403761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178548709694739635602507 267823064542109453403761)
        ·
          refine ⟨200867298406582090052821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267823064542109453403761 200867298406582090052821)
          ·
            refine ⟨4707827306404267735613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 200867298406582090052821 4707827306404267735613)
            ·
              rfl

theorem cell20_278492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 7].length) (baseStart_278492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278492 prefixEnd_278492 := by exact prefixLift 278492
  have htrace : WordTrace (prefixWord ++ tailWord_278492) baseStart_278492 baseEnd_278492 := by
    simpa [prefixWord, tailWord_278492, baseEnd_278492] using wordTrace_append hprefix tailTrace_278492
  have hstable : (prefixWord ++ tailWord_278492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278492).length < 2 ^ (prefixWord ++ tailWord_278492).sum := by decide
  have hdescent : baseEnd_278492 < baseStart_278492 := by decide
  rcases family_descends (prefixWord ++ tailWord_278492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278513 : List Nat := [1, 2, 2, 2, 6, 1, 1, 5]
def baseStart_278513 : Nat := 118140960795 + 278513 * 2 ^ 59
def prefixEnd_278513 : Nat := 4983230072969 + 3 ^ 40 * 278513 * 2
def baseEnd_278513 : Nat := 42373640748377496387155

theorem tailTrace_278513 : CollatzResearch.WordTrace tailWord_278513 prefixEnd_278513 42373640748377496387155 := by
  unfold tailWord_278513
  simp only [CollatzResearch.WordTrace]
  refine ⟨10158203640002442078568193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6772135760001628052378795 10158203640002442078568193)
  ·
    refine ⟨7618652730001831558926145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10158203640002442078568193 7618652730001831558926145)
    ·
      refine ⟨5713989547501373669194609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7618652730001831558926145 5713989547501373669194609)
      ·
        refine ⟨4285492160626030251895957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5713989547501373669194609 4285492160626030251895957)
        ·
          refine ⟨200882445029345168057623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4285492160626030251895957 200882445029345168057623)
          ·
            refine ⟨301323667544017752086435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200882445029345168057623 301323667544017752086435)
            ·
              refine ⟨451985501316026628129653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301323667544017752086435 451985501316026628129653)
              ·
                refine ⟨42373640748377496387155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 451985501316026628129653 42373640748377496387155)
                ·
                  rfl

theorem cell20_278513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 5].length) (baseStart_278513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278513 prefixEnd_278513 := by exact prefixLift 278513
  have htrace : WordTrace (prefixWord ++ tailWord_278513) baseStart_278513 baseEnd_278513 := by
    simpa [prefixWord, tailWord_278513, baseEnd_278513] using wordTrace_append hprefix tailTrace_278513
  have hstable : (prefixWord ++ tailWord_278513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278513).length < 2 ^ (prefixWord ++ tailWord_278513).sum := by decide
  have hdescent : baseEnd_278513 < baseStart_278513 := by decide
  rcases family_descends (prefixWord ++ tailWord_278513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278565 : List Nat := [1, 3, 1, 2, 2, 3, 2, 4, 2]
def baseStart_278565 : Nat := 118140960795 + 278565 * 2 ^ 59
def prefixEnd_278565 : Nat := 4983230072969 + 3 ^ 40 * 278565 * 2
def baseEnd_278565 : Nat := 127144656462051419427919

theorem tailTrace_278565 : CollatzResearch.WordTrace tailWord_278565 prefixEnd_278565 127144656462051419427919 := by
  unfold tailWord_278565
  simp only [CollatzResearch.WordTrace]
  refine ⟨10160100235814054959461149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6773400157209369972974099 10160100235814054959461149)
  ·
    refine ⟨3810037588430270609797931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10160100235814054959461149 3810037588430270609797931)
    ·
      refine ⟨5715056382645405914696897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3810037588430270609797931 5715056382645405914696897)
      ·
        refine ⟨4286292286984054436022673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5715056382645405914696897 4286292286984054436022673)
        ·
          refine ⟨3214719215238040827017005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4286292286984054436022673 3214719215238040827017005)
          ·
            refine ⟨1205519705714265310131377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3214719215238040827017005 1205519705714265310131377)
            ·
              refine ⟨904139779285698982598533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1205519705714265310131377 904139779285698982598533)
              ·
                refine ⟨169526208616068559237225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 904139779285698982598533 169526208616068559237225)
                ·
                  refine ⟨127144656462051419427919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169526208616068559237225 127144656462051419427919)
                  ·
                    rfl

theorem cell20_278565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_278565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278565 prefixEnd_278565 := by exact prefixLift 278565
  have htrace : WordTrace (prefixWord ++ tailWord_278565) baseStart_278565 baseEnd_278565 := by
    simpa [prefixWord, tailWord_278565, baseEnd_278565] using wordTrace_append hprefix tailTrace_278565
  have hstable : (prefixWord ++ tailWord_278565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278565).length < 2 ^ (prefixWord ++ tailWord_278565).sum := by decide
  have hdescent : baseEnd_278565 < baseStart_278565 := by decide
  rcases family_descends (prefixWord ++ tailWord_278565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278610 : List Nat := [3, 2, 2, 1, 4, 2, 6]
def baseStart_278610 : Nat := 118140960795 + 278610 * 2 ^ 59
def prefixEnd_278610 : Nat := 4983230072969 + 3 ^ 40 * 278610 * 2
def baseEnd_278610 : Nat := 14129466187581251436415

theorem tailTrace_278610 : CollatzResearch.WordTrace tailWord_278610 prefixEnd_278610 14129466187581251436415 := by
  unfold tailWord_278610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540435380162756911212321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6774494347100685096566189 2540435380162756911212321)
  ·
    refine ⟨1905326535122067683409241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2540435380162756911212321 1905326535122067683409241)
    ·
      refine ⟨1428994901341550762556931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1905326535122067683409241 1428994901341550762556931)
      ·
        refine ⟨2143492352012326143835397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428994901341550762556931 2143492352012326143835397)
        ·
          refine ⟨401904816002311151969137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2143492352012326143835397 401904816002311151969137)
          ·
            refine ⟨301428612001733363976853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401904816002311151969137 301428612001733363976853)
            ·
              refine ⟨14129466187581251436415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 301428612001733363976853 14129466187581251436415)
              ·
                rfl

theorem cell20_278610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 6].length) (baseStart_278610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278610 prefixEnd_278610 := by exact prefixLift 278610
  have htrace : WordTrace (prefixWord ++ tailWord_278610) baseStart_278610 baseEnd_278610 := by
    simpa [prefixWord, tailWord_278610, baseEnd_278610] using wordTrace_append hprefix tailTrace_278610
  have hstable : (prefixWord ++ tailWord_278610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278610).length < 2 ^ (prefixWord ++ tailWord_278610).sum := by decide
  have hdescent : baseEnd_278610 < baseStart_278610 := by decide
  rcases family_descends (prefixWord ++ tailWord_278610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278624 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_278624 : Nat := 118140960795 + 278624 * 2 ^ 59
def prefixEnd_278624 : Nat := 4983230072969 + 3 ^ 40 * 278624 * 2
def baseEnd_278624 : Nat := 127171585669709436461011

theorem tailTrace_278624 : CollatzResearch.WordTrace tailWord_278624 prefixEnd_278624 127171585669709436461011 := by
  unfold tailWord_278624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5081126071300154017929463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6774834761733538690572617 5081126071300154017929463)
  ·
    refine ⟨7621689106950231026894195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5081126071300154017929463 7621689106950231026894195)
    ·
      refine ⟨11432533660425346540341293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7621689106950231026894195 11432533660425346540341293)
      ·
        refine ⟨4287200122659504952627985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11432533660425346540341293 4287200122659504952627985)
        ·
          refine ⟨3215400091994628714470989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4287200122659504952627985 3215400091994628714470989)
          ·
            refine ⟨1205775034497985767926621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3215400091994628714470989 1205775034497985767926621)
            ·
              refine ⟨452165637936744662972483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1205775034497985767926621 452165637936744662972483)
              ·
                refine ⟨678248456905116994458725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452165637936744662972483 678248456905116994458725)
                ·
                  refine ⟨127171585669709436461011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 678248456905116994458725 127171585669709436461011)
                  ·
                    rfl

theorem cell20_278624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_278624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278624 prefixEnd_278624 := by exact prefixLift 278624
  have htrace : WordTrace (prefixWord ++ tailWord_278624) baseStart_278624 baseEnd_278624 := by
    simpa [prefixWord, tailWord_278624, baseEnd_278624] using wordTrace_append hprefix tailTrace_278624
  have hstable : (prefixWord ++ tailWord_278624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278624).length < 2 ^ (prefixWord ++ tailWord_278624).sum := by decide
  have hdescent : baseEnd_278624 < baseStart_278624 := by decide
  rcases family_descends (prefixWord ++ tailWord_278624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278631 : List Nat := [1, 1, 5, 1, 1, 2, 4, 5]
def baseStart_278631 : Nat := 118140960795 + 278631 * 2 ^ 59
def prefixEnd_278631 : Nat := 4983230072969 + 3 ^ 40 * 278631 * 2
def baseEnd_278631 : Nat := 42391593553482841075883

theorem tailTrace_278631 : CollatzResearch.WordTrace tailWord_278631 prefixEnd_278631 42391593553482841075883 := by
  unfold tailWord_278631
  simp only [CollatzResearch.WordTrace]
  refine ⟨10162507453574948231363747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6775004969049965487575831 10162507453574948231363747)
  ·
    refine ⟨15243761180362422347045621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10162507453574948231363747 15243761180362422347045621)
    ·
      refine ⟨1429102610658977095035527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15243761180362422347045621 1429102610658977095035527)
      ·
        refine ⟨2143653915988465642553291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429102610658977095035527 2143653915988465642553291)
        ·
          refine ⟨3215480873982698463829937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2143653915988465642553291 3215480873982698463829937)
          ·
            refine ⟨2411610655487023847872453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3215480873982698463829937 2411610655487023847872453)
            ·
              refine ⟨452176997903816971476085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2411610655487023847872453 452176997903816971476085)
              ·
                refine ⟨42391593553482841075883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 452176997903816971476085 42391593553482841075883)
                ·
                  rfl

theorem cell20_278631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_278631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278631 prefixEnd_278631 := by exact prefixLift 278631
  have htrace : WordTrace (prefixWord ++ tailWord_278631) baseStart_278631 baseEnd_278631 := by
    simpa [prefixWord, tailWord_278631, baseEnd_278631] using wordTrace_append hprefix tailTrace_278631
  have hstable : (prefixWord ++ tailWord_278631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278631).length < 2 ^ (prefixWord ++ tailWord_278631).sum := by decide
  have hdescent : baseEnd_278631 < baseStart_278631 := by decide
  rcases family_descends (prefixWord ++ tailWord_278631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278634 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_278634 : Nat := 118140960795 + 278634 * 2 ^ 59
def prefixEnd_278634 : Nat := 4983230072969 + 3 ^ 40 * 278634 * 2
def baseEnd_278634 : Nat := 127176149942193846127637

theorem tailTrace_278634 : CollatzResearch.WordTrace tailWord_278634 prefixEnd_278634 127176149942193846127637 := by
  unfold tailWord_278634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540654218141019935930739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6775077915042719829148637 2540654218141019935930739)
  ·
    refine ⟨3810981327211529903896109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2540654218141019935930739 3810981327211529903896109)
    ·
      refine ⟨1429117997704323713961041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3810981327211529903896109 1429117997704323713961041)
      ·
        refine ⟨1071838498278242785470781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1429117997704323713961041 1071838498278242785470781)
        ·
          refine ⟨401939436854341044551543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1071838498278242785470781 401939436854341044551543)
          ·
            refine ⟨602909155281511566827315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401939436854341044551543 602909155281511566827315)
            ·
              refine ⟨904363732922267350240973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602909155281511566827315 904363732922267350240973)
              ·
                refine ⟨339136399845850256340365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 904363732922267350240973 339136399845850256340365)
                ·
                  refine ⟨127176149942193846127637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339136399845850256340365 127176149942193846127637)
                  ·
                    rfl

theorem cell20_278634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_278634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278634 prefixEnd_278634 := by exact prefixLift 278634
  have htrace : WordTrace (prefixWord ++ tailWord_278634) baseStart_278634 baseEnd_278634 := by
    simpa [prefixWord, tailWord_278634, baseEnd_278634] using wordTrace_append hprefix tailTrace_278634
  have hstable : (prefixWord ++ tailWord_278634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278634).length < 2 ^ (prefixWord ++ tailWord_278634).sum := by decide
  have hdescent : baseEnd_278634 < baseStart_278634 := by decide
  rcases family_descends (prefixWord ++ tailWord_278634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278678 : List Nat := [5, 3, 2, 1, 1, 2, 1, 5]
def baseStart_278678 : Nat := 118140960795 + 278678 * 2 ^ 59
def prefixEnd_278678 : Nat := 4983230072969 + 3 ^ 40 * 278678 * 2
def baseEnd_278678 : Nat := 42398744247041749553597

theorem tailTrace_278678 : CollatzResearch.WordTrace tailWord_278678 prefixEnd_278678 42398744247041749553597 := by
  unfold tailWord_278678
  simp only [CollatzResearch.WordTrace]
  refine ⟨635263855275292203645293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6776147789603116838883125 635263855275292203645293)
  ·
    refine ⟨238223945728234576366985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 635263855275292203645293 238223945728234576366985)
    ·
      refine ⟨178667959296175932275239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238223945728234576366985 178667959296175932275239)
      ·
        refine ⟨268001938944263898412859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178667959296175932275239 268001938944263898412859)
        ·
          refine ⟨402002908416395847619289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268001938944263898412859 402002908416395847619289)
          ·
            refine ⟨301502181312296885714467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402002908416395847619289 301502181312296885714467)
            ·
              refine ⟨452253271968445328571701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301502181312296885714467 452253271968445328571701)
              ·
                refine ⟨42398744247041749553597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 452253271968445328571701 42398744247041749553597)
                ·
                  rfl

theorem cell20_278678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_278678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278678 prefixEnd_278678 := by exact prefixLift 278678
  have htrace : WordTrace (prefixWord ++ tailWord_278678) baseStart_278678 baseEnd_278678 := by
    simpa [prefixWord, tailWord_278678, baseEnd_278678] using wordTrace_append hprefix tailTrace_278678
  have hstable : (prefixWord ++ tailWord_278678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278678).length < 2 ^ (prefixWord ++ tailWord_278678).sum := by decide
  have hdescent : baseEnd_278678 < baseStart_278678 := by decide
  rcases family_descends (prefixWord ++ tailWord_278678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278738 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_278738 : Nat := 118140960795 + 278738 * 2 ^ 59
def prefixEnd_278738 : Nat := 4983230072969 + 3 ^ 40 * 278738 * 2
def baseEnd_278738 : Nat := 127223618376031706660545

theorem tailTrace_278738 : CollatzResearch.WordTrace tailWord_278738 prefixEnd_278738 127223618376031706660545 := by
  unfold tailWord_278738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2541602516046826376377217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6777606709458203670339245 2541602516046826376377217)
  ·
    refine ⟨1906201887035119782282913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2541602516046826376377217 1906201887035119782282913)
    ·
      refine ⟨1429651415276339836712185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1906201887035119782282913 1429651415276339836712185)
      ·
        refine ⟨1072238561457254877534139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1429651415276339836712185 1072238561457254877534139)
        ·
          refine ⟨1608357842185882316301209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072238561457254877534139 1608357842185882316301209)
          ·
            refine ⟨1206268381639411737225907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1608357842185882316301209 1206268381639411737225907)
            ·
              refine ⟨1809402572459117605838861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206268381639411737225907 1809402572459117605838861)
              ·
                refine ⟨678525964672169102189573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1809402572459117605838861 678525964672169102189573)
                ·
                  refine ⟨127223618376031706660545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 678525964672169102189573 127223618376031706660545)
                  ·
                    rfl

theorem cell20_278738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_278738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278738 prefixEnd_278738 := by exact prefixLift 278738
  have htrace : WordTrace (prefixWord ++ tailWord_278738) baseStart_278738 baseEnd_278738 := by
    simpa [prefixWord, tailWord_278738, baseEnd_278738] using wordTrace_append hprefix tailTrace_278738
  have hstable : (prefixWord ++ tailWord_278738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278738).length < 2 ^ (prefixWord ++ tailWord_278738).sum := by decide
  have hdescent : baseEnd_278738 < baseStart_278738 := by decide
  rcases family_descends (prefixWord ++ tailWord_278738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278754 : List Nat := [3, 3, 4, 1, 2, 1, 2, 4]
def baseStart_278754 : Nat := 118140960795 + 278754 * 2 ^ 59
def prefixEnd_278754 : Nat := 4983230072969 + 3 ^ 40 * 278754 * 2
def baseEnd_278754 : Nat := 42410307070668920709049

theorem tailTrace_278754 : CollatzResearch.WordTrace tailWord_278754 prefixEnd_278754 42410307070668920709049 := by
  unfold tailWord_278754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2541748408032335059522829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6777995754752893492060877 2541748408032335059522829)
  ·
    refine ⟨953155653012125647321061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2541748408032335059522829 953155653012125647321061)
    ·
      refine ⟨178716684939773558872699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 953155653012125647321061 178716684939773558872699)
      ·
        refine ⟨268075027409660338309049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178716684939773558872699 268075027409660338309049)
        ·
          refine ⟨201056270557245253731787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268075027409660338309049 201056270557245253731787)
          ·
            refine ⟨301584405835867880597681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201056270557245253731787 301584405835867880597681)
            ·
              refine ⟨226188304376900910448261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301584405835867880597681 226188304376900910448261)
              ·
                refine ⟨42410307070668920709049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 226188304376900910448261 42410307070668920709049)
                ·
                  rfl

theorem cell20_278754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_278754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278754 prefixEnd_278754 := by exact prefixLift 278754
  have htrace : WordTrace (prefixWord ++ tailWord_278754) baseStart_278754 baseEnd_278754 := by
    simpa [prefixWord, tailWord_278754, baseEnd_278754] using wordTrace_append hprefix tailTrace_278754
  have hstable : (prefixWord ++ tailWord_278754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278754).length < 2 ^ (prefixWord ++ tailWord_278754).sum := by decide
  have hdescent : baseEnd_278754 < baseStart_278754 := by decide
  rcases family_descends (prefixWord ++ tailWord_278754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278807 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 3]
def baseStart_278807 : Nat := 118140960795 + 278807 * 2 ^ 59
def prefixEnd_278807 : Nat := 4983230072969 + 3 ^ 40 * 278807 * 2
def baseEnd_278807 : Nat := 127255111856174133360263

theorem tailTrace_278807 : CollatzResearch.WordTrace tailWord_278807 prefixEnd_278807 127255111856174133360263 := by
  unfold tailWord_278807
  simp only [CollatzResearch.WordTrace]
  refine ⟨10168926700937330289770675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6779284467291553526513783 10168926700937330289770675)
  ·
    refine ⟨15253390051405995434656013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10168926700937330289770675 15253390051405995434656013)
    ·
      refine ⟨5720021269277248287996005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15253390051405995434656013 5720021269277248287996005)
      ·
        refine ⟨1072503987989484053999251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5720021269277248287996005 1072503987989484053999251)
        ·
          refine ⟨1608755981984226080998877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072503987989484053999251 1608755981984226080998877)
          ·
            refine ⟨603283493244084780374579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1608755981984226080998877 603283493244084780374579)
            ·
              refine ⟨904925239866127170561869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603283493244084780374579 904925239866127170561869)
              ·
                refine ⟨339346964949797688960701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 904925239866127170561869 339346964949797688960701)
                ·
                  refine ⟨127255111856174133360263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339346964949797688960701 127255111856174133360263)
                  ·
                    rfl

theorem cell20_278807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 3].length) (baseStart_278807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278807 prefixEnd_278807 := by exact prefixLift 278807
  have htrace : WordTrace (prefixWord ++ tailWord_278807) baseStart_278807 baseEnd_278807 := by
    simpa [prefixWord, tailWord_278807, baseEnd_278807] using wordTrace_append hprefix tailTrace_278807
  have hstable : (prefixWord ++ tailWord_278807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278807).length < 2 ^ (prefixWord ++ tailWord_278807).sum := by decide
  have hdescent : baseEnd_278807 < baseStart_278807 := by decide
  rcases family_descends (prefixWord ++ tailWord_278807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278842 : List Nat := [3, 1, 1, 1, 4, 10]
def baseStart_278842 : Nat := 118140960795 + 278842 * 2 ^ 59
def prefixEnd_278842 : Nat := 4983230072969 + 3 ^ 40 * 278842 * 2
def baseEnd_278842 : Nat := 4713743955921095081239

theorem tailTrace_278842 : CollatzResearch.WordTrace tailWord_278842 prefixEnd_278842 4713743955921095081239 := by
  unfold tailWord_278842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2542550813952632816823695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6780135503873687511529853 2542550813952632816823695)
  ·
    refine ⟨3813826220928949225235543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2542550813952632816823695 3813826220928949225235543)
    ·
      refine ⟨5720739331393423837853315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3813826220928949225235543 5720739331393423837853315)
      ·
        refine ⟨8581108997090135756779973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5720739331393423837853315 8581108997090135756779973)
        ·
          refine ⟨1608957936954400454396245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8581108997090135756779973 1608957936954400454396245)
          ·
            refine ⟨4713743955921095081239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1608957936954400454396245 4713743955921095081239)
            ·
              rfl

theorem cell20_278842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 10].length) (baseStart_278842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278842 prefixEnd_278842 := by exact prefixLift 278842
  have htrace : WordTrace (prefixWord ++ tailWord_278842) baseStart_278842 baseEnd_278842 := by
    simpa [prefixWord, tailWord_278842, baseEnd_278842] using wordTrace_append hprefix tailTrace_278842
  have hstable : (prefixWord ++ tailWord_278842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278842).length < 2 ^ (prefixWord ++ tailWord_278842).sum := by decide
  have hdescent : baseEnd_278842 < baseStart_278842 := by decide
  rcases family_descends (prefixWord ++ tailWord_278842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278935 : List Nat := [1, 1, 3, 3, 1, 1, 6, 4]
def baseStart_278935 : Nat := 118140960795 + 278935 * 2 ^ 59
def prefixEnd_278935 : Nat := 4983230072969 + 3 ^ 40 * 278935 * 2
def baseEnd_278935 : Nat := 42437844847991525697691

theorem tailTrace_278935 : CollatzResearch.WordTrace tailWord_278935 prefixEnd_278935 42437844847991525697691 := by
  unfold tailWord_278935
  simp only [CollatzResearch.WordTrace]
  refine ⟨10173595244473608150430259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6782396829649072100286839 10173595244473608150430259)
  ·
    refine ⟨15260392866710412225645389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10173595244473608150430259 15260392866710412225645389)
    ·
      refine ⟨5722647325016404584617021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15260392866710412225645389 5722647325016404584617021)
      ·
        refine ⟨2145992746881151719231383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5722647325016404584617021 2145992746881151719231383)
        ·
          refine ⟨3218989120321727578847075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145992746881151719231383 3218989120321727578847075)
          ·
            refine ⟨4828483680482591368270613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3218989120321727578847075 4828483680482591368270613)
            ·
              refine ⟨226335172522621470387685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4828483680482591368270613 226335172522621470387685)
              ·
                refine ⟨42437844847991525697691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 226335172522621470387685 42437844847991525697691)
                ·
                  rfl

theorem cell20_278935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 4].length) (baseStart_278935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278935 prefixEnd_278935 := by exact prefixLift 278935
  have htrace : WordTrace (prefixWord ++ tailWord_278935) baseStart_278935 baseEnd_278935 := by
    simpa [prefixWord, tailWord_278935, baseEnd_278935] using wordTrace_append hprefix tailTrace_278935
  have hstable : (prefixWord ++ tailWord_278935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278935).length < 2 ^ (prefixWord ++ tailWord_278935).sum := by decide
  have hdescent : baseEnd_278935 < baseStart_278935 := by decide
  rcases family_descends (prefixWord ++ tailWord_278935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278941 : List Nat := [1, 4, 2, 1, 5, 1, 1, 3, 2]
def baseStart_278941 : Nat := 118140960795 + 278941 * 2 ^ 59
def prefixEnd_278941 : Nat := 4983230072969 + 3 ^ 40 * 278941 * 2
def baseEnd_278941 : Nat := 127316273107465222893049

theorem tailTrace_278941 : CollatzResearch.WordTrace tailWord_278941 prefixEnd_278941 127316273107465222893049 := by
  unfold tailWord_278941
  simp only [CollatzResearch.WordTrace]
  refine ⟨10173814082451871175148677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6782542721634580783432451 10173814082451871175148677)
  ·
    refine ⟨1907590140459725845340377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10173814082451871175148677 1907590140459725845340377)
    ·
      refine ⟨1430692605344794384005283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1907590140459725845340377 1430692605344794384005283)
      ·
        refine ⟨2146038908017191576007925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430692605344794384005283 2146038908017191576007925)
        ·
          refine ⟨201191147626611710250743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2146038908017191576007925 201191147626611710250743)
          ·
            refine ⟨301786721439917565376115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201191147626611710250743 301786721439917565376115)
            ·
              refine ⟨452680082159876348064173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301786721439917565376115 452680082159876348064173)
              ·
                refine ⟨169755030809953630524065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452680082159876348064173 169755030809953630524065)
                ·
                  refine ⟨127316273107465222893049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169755030809953630524065 127316273107465222893049)
                  ·
                    rfl

theorem cell20_278941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_278941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278941 prefixEnd_278941 := by exact prefixLift 278941
  have htrace : WordTrace (prefixWord ++ tailWord_278941) baseStart_278941 baseEnd_278941 := by
    simpa [prefixWord, tailWord_278941, baseEnd_278941] using wordTrace_append hprefix tailTrace_278941
  have hstable : (prefixWord ++ tailWord_278941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278941).length < 2 ^ (prefixWord ++ tailWord_278941).sum := by decide
  have hdescent : baseEnd_278941 < baseStart_278941 := by decide
  rcases family_descends (prefixWord ++ tailWord_278941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278952 : List Nat := [2, 1, 6, 1, 1, 3, 6]
def baseStart_278952 : Nat := 118140960795 + 278952 * 2 ^ 59
def prefixEnd_278952 : Nat := 4983230072969 + 3 ^ 40 * 278952 * 2
def baseEnd_278952 : Nat := 14146810423022008169593

theorem tailTrace_278952 : CollatzResearch.WordTrace tailWord_278952 prefixEnd_278952 14146810423022008169593 := by
  unfold tailWord_278952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5087107642706010026899555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6782810190274680035866073 5087107642706010026899555)
  ·
    refine ⟨7630661464059015040349333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5087107642706010026899555 7630661464059015040349333)
    ·
      refine ⟨357687256127766330016375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7630661464059015040349333 357687256127766330016375)
      ·
        refine ⟨536530884191649495024563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357687256127766330016375 536530884191649495024563)
        ·
          refine ⟨804796326287474242536845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536530884191649495024563 804796326287474242536845)
          ·
            refine ⟨301798622357802840951317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 804796326287474242536845 301798622357802840951317)
            ·
              refine ⟨14146810423022008169593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 301798622357802840951317 14146810423022008169593)
              ·
                rfl

theorem cell20_278952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 6].length) (baseStart_278952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278952 prefixEnd_278952 := by exact prefixLift 278952
  have htrace : WordTrace (prefixWord ++ tailWord_278952) baseStart_278952 baseEnd_278952 := by
    simpa [prefixWord, tailWord_278952, baseEnd_278952] using wordTrace_append hprefix tailTrace_278952
  have hstable : (prefixWord ++ tailWord_278952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278952).length < 2 ^ (prefixWord ++ tailWord_278952).sum := by decide
  have hdescent : baseEnd_278952 < baseStart_278952 := by decide
  rcases family_descends (prefixWord ++ tailWord_278952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278973 : List Nat := [1, 4, 1, 2, 2, 3, 2, 5]
def baseStart_278973 : Nat := 118140960795 + 278973 * 2 ^ 59
def prefixEnd_278973 : Nat := 4983230072969 + 3 ^ 40 * 278973 * 2
def baseEnd_278973 : Nat := 42443626259805111275417

theorem tailTrace_278973 : CollatzResearch.WordTrace tailWord_278973 prefixEnd_278973 42443626259805111275417 := by
  unfold tailWord_278973
  simp only [CollatzResearch.WordTrace]
  refine ⟨10174981218335940640313573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6783320812223960426875715 10174981218335940640313573)
  ·
    refine ⟨1907808978437988870058795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10174981218335940640313573 1907808978437988870058795)
    ·
      refine ⟨2861713467656983305088193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907808978437988870058795 2861713467656983305088193)
      ·
        refine ⟨2146285100742737478816145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2861713467656983305088193 2146285100742737478816145)
        ·
          refine ⟨1609713825557053109112109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2146285100742737478816145 1609713825557053109112109)
          ·
            refine ⟨603642684583894915917041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1609713825557053109112109 603642684583894915917041)
            ·
              refine ⟨452732013437921186937781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603642684583894915917041 452732013437921186937781)
              ·
                refine ⟨42443626259805111275417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 452732013437921186937781 42443626259805111275417)
                ·
                  rfl

theorem cell20_278973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_278973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_278973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_278973 prefixEnd_278973 := by exact prefixLift 278973
  have htrace : WordTrace (prefixWord ++ tailWord_278973) baseStart_278973 baseEnd_278973 := by
    simpa [prefixWord, tailWord_278973, baseEnd_278973] using wordTrace_append hprefix tailTrace_278973
  have hstable : (prefixWord ++ tailWord_278973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278973).length < 2 ^ (prefixWord ++ tailWord_278973).sum := by decide
  have hdescent : baseEnd_278973 < baseStart_278973 := by decide
  rcases family_descends (prefixWord ++ tailWord_278973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279011 : List Nat := [1, 1, 1, 6, 4, 7]
def baseStart_279011 : Nat := 118140960795 + 279011 * 2 ^ 59
def prefixEnd_279011 : Nat := 4983230072969 + 3 ^ 40 * 279011 * 2
def baseEnd_279011 : Nat := 4716600852402077428127

theorem tailTrace_279011 : CollatzResearch.WordTrace tailWord_279011 prefixEnd_279011 4716600852402077428127 := by
  unfold tailWord_279011
  simp only [CollatzResearch.WordTrace]
  refine ⟨10176367192198273130196887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6784244794798848753464591 10176367192198273130196887)
  ·
    refine ⟨15264550788297409695295331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10176367192198273130196887 15264550788297409695295331)
    ·
      refine ⟨22896826182446114542942997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15264550788297409695295331 22896826182446114542942997)
      ·
        refine ⟨1073288727302161619200453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22896826182446114542942997 1073288727302161619200453)
        ·
          refine ⟨201241636369155303600085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1073288727302161619200453 201241636369155303600085)
          ·
            refine ⟨4716600852402077428127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 201241636369155303600085 4716600852402077428127)
            ·
              rfl

theorem cell20_279011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 7].length) (baseStart_279011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279011 prefixEnd_279011 := by exact prefixLift 279011
  have htrace : WordTrace (prefixWord ++ tailWord_279011) baseStart_279011 baseEnd_279011 := by
    simpa [prefixWord, tailWord_279011, baseEnd_279011] using wordTrace_append hprefix tailTrace_279011
  have hstable : (prefixWord ++ tailWord_279011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279011).length < 2 ^ (prefixWord ++ tailWord_279011).sum := by decide
  have hdescent : baseEnd_279011 < baseStart_279011 := by decide
  rcases family_descends (prefixWord ++ tailWord_279011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279025 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_279025 : Nat := 118140960795 + 279025 * 2 ^ 59
def prefixEnd_279025 : Nat := 4983230072969 + 3 ^ 40 * 279025 * 2
def baseEnd_279025 : Nat := 127354612996334264092705

theorem tailTrace_279025 : CollatzResearch.WordTrace tailWord_279025 prefixEnd_279025 127354612996334264092705 := by
  unfold tailWord_279025
  simp only [CollatzResearch.WordTrace]
  refine ⟨10176877814147553521206529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6784585209431702347471019 10176877814147553521206529)
  ·
    refine ⟨7632658360610665140904897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10176877814147553521206529 7632658360610665140904897)
    ·
      refine ⟨5724493770457998855678673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7632658360610665140904897 5724493770457998855678673)
      ·
        refine ⟨4293370327843499141759005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5724493770457998855678673 4293370327843499141759005)
        ·
          refine ⟨1610013872941312178159627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4293370327843499141759005 1610013872941312178159627)
          ·
            refine ⟨2415020809411968267239441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610013872941312178159627 2415020809411968267239441)
            ·
              refine ⟨1811265607058976200429581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2415020809411968267239441 1811265607058976200429581)
              ·
                refine ⟨679224602647116075161093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1811265607058976200429581 679224602647116075161093)
                ·
                  refine ⟨127354612996334264092705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679224602647116075161093 127354612996334264092705)
                  ·
                    rfl

theorem cell20_279025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_279025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279025 prefixEnd_279025 := by exact prefixLift 279025
  have htrace : WordTrace (prefixWord ++ tailWord_279025) baseStart_279025 baseEnd_279025 := by
    simpa [prefixWord, tailWord_279025, baseEnd_279025] using wordTrace_append hprefix tailTrace_279025
  have hstable : (prefixWord ++ tailWord_279025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279025).length < 2 ^ (prefixWord ++ tailWord_279025).sum := by decide
  have hdescent : baseEnd_279025 < baseStart_279025 := by decide
  rcases family_descends (prefixWord ++ tailWord_279025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279080 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_279080 : Nat := 118140960795 + 279080 * 2 ^ 59
def prefixEnd_279080 : Nat := 4983230072969 + 3 ^ 40 * 279080 * 2
def baseEnd_279080 : Nat := 127379716494998517259147

theorem tailTrace_279080 : CollatzResearch.WordTrace tailWord_279080 prefixEnd_279080 127379716494998517259147 := by
  unfold tailWord_279080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089441914474148957229347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6785922552632198609639129 5089441914474148957229347)
  ·
    refine ⟨7634162871711223435844021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5089441914474148957229347 7634162871711223435844021)
    ·
      refine ⟨715702769222927197110377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7634162871711223435844021 715702769222927197110377)
      ·
        refine ⟨536777076917195397832783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 715702769222927197110377 536777076917195397832783)
        ·
          refine ⟨805165615375793096749175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536777076917195397832783 805165615375793096749175)
          ·
            refine ⟨1207748423063689645123763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805165615375793096749175 1207748423063689645123763)
            ·
              refine ⟨1811622634595534467685645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207748423063689645123763 1811622634595534467685645)
              ·
                refine ⟨679358487973325425382117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1811622634595534467685645 679358487973325425382117)
                ·
                  refine ⟨127379716494998517259147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679358487973325425382117 127379716494998517259147)
                  ·
                    rfl

theorem cell20_279080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_279080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279080 prefixEnd_279080 := by exact prefixLift 279080
  have htrace : WordTrace (prefixWord ++ tailWord_279080) baseStart_279080 baseEnd_279080 := by
    simpa [prefixWord, tailWord_279080, baseEnd_279080] using wordTrace_append hprefix tailTrace_279080
  have hstable : (prefixWord ++ tailWord_279080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279080).length < 2 ^ (prefixWord ++ tailWord_279080).sum := by decide
  have hdescent : baseEnd_279080 < baseStart_279080 := by decide
  rcases family_descends (prefixWord ++ tailWord_279080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279115 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_279115 : Nat := 118140960795 + 279115 * 2 ^ 59
def prefixEnd_279115 : Nat := 4983230072969 + 3 ^ 40 * 279115 * 2
def baseEnd_279115 : Nat := 127395691448693951092337

theorem tailTrace_279115 : CollatzResearch.WordTrace tailWord_279115 prefixEnd_279115 127395691448693951092337 := by
  unfold tailWord_279115
  simp only [CollatzResearch.WordTrace]
  refine ⟨10180160383821498891982799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6786773589214332594655199 10180160383821498891982799)
  ·
    refine ⟨15270240575732248337974199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10180160383821498891982799 15270240575732248337974199)
    ·
      refine ⟨22905360863598372506961299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15270240575732248337974199 22905360863598372506961299)
      ·
        refine ⟨34358041295397558760441949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22905360863598372506961299 34358041295397558760441949)
        ·
          refine ⟨12884265485774084535165731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34358041295397558760441949 12884265485774084535165731)
          ·
            refine ⟨19326398228661126802748597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12884265485774084535165731 19326398228661126802748597)
            ·
              refine ⟨1811849833936980637757681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19326398228661126802748597 1811849833936980637757681)
              ·
                refine ⟨1358887375452735478318261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1811849833936980637757681 1358887375452735478318261)
                ·
                  refine ⟨127395691448693951092337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1358887375452735478318261 127395691448693951092337)
                  ·
                    rfl

theorem cell20_279115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_279115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279115 prefixEnd_279115 := by exact prefixLift 279115
  have htrace : WordTrace (prefixWord ++ tailWord_279115) baseStart_279115 baseEnd_279115 := by
    simpa [prefixWord, tailWord_279115, baseEnd_279115] using wordTrace_append hprefix tailTrace_279115
  have hstable : (prefixWord ++ tailWord_279115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279115).length < 2 ^ (prefixWord ++ tailWord_279115).sum := by decide
  have hdescent : baseEnd_279115 < baseStart_279115 := by decide
  rcases family_descends (prefixWord ++ tailWord_279115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279149 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 3]
def baseStart_279149 : Nat := 118140960795 + 279149 * 2 ^ 59
def prefixEnd_279149 : Nat := 4983230072969 + 3 ^ 40 * 279149 * 2
def baseEnd_279149 : Nat := 127411209975140943958865

theorem tailTrace_279149 : CollatzResearch.WordTrace tailWord_279149 prefixEnd_279149 127411209975140943958865 := by
  unfold tailWord_279149
  simp only [CollatzResearch.WordTrace]
  refine ⟨10181400465698322698720501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6787600310465548465813667 10181400465698322698720501)
  ·
    refine ⟨954506293659217753005047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10181400465698322698720501 954506293659217753005047)
    ·
      refine ⟨1431759440488826629507571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 954506293659217753005047 1431759440488826629507571)
      ·
        refine ⟨2147639160733239944261357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1431759440488826629507571 2147639160733239944261357)
        ·
          refine ⟨805364685274964979098009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2147639160733239944261357 805364685274964979098009)
          ·
            refine ⟨604023513956223734323507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 805364685274964979098009 604023513956223734323507)
            ·
              refine ⟨906035270934335601485261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604023513956223734323507 906035270934335601485261)
              ·
                refine ⟨339763226600375850556973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 906035270934335601485261 339763226600375850556973)
                ·
                  refine ⟨127411209975140943958865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339763226600375850556973 127411209975140943958865)
                  ·
                    rfl

theorem cell20_279149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_279149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279149 prefixEnd_279149 := by exact prefixLift 279149
  have htrace : WordTrace (prefixWord ++ tailWord_279149) baseStart_279149 baseEnd_279149 := by
    simpa [prefixWord, tailWord_279149, baseEnd_279149] using wordTrace_append hprefix tailTrace_279149
  have hstable : (prefixWord ++ tailWord_279149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279149).length < 2 ^ (prefixWord ++ tailWord_279149).sum := by decide
  have hdescent : baseEnd_279149 < baseStart_279149 := by decide
  rcases family_descends (prefixWord ++ tailWord_279149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279215 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 4]
def baseStart_279215 : Nat := 118140960795 + 279215 * 2 ^ 59
def prefixEnd_279215 : Nat := 4983230072969 + 3 ^ 40 * 279215 * 2
def baseEnd_279215 : Nat := 127441334173538047758595

theorem tailTrace_279215 : CollatzResearch.WordTrace tailWord_279215 prefixEnd_279215 127441334173538047758595 := by
  unfold tailWord_279215
  simp only [CollatzResearch.WordTrace]
  refine ⟨10183807683459215970623099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6789205122306143980415399 10183807683459215970623099)
  ·
    refine ⟨15275711525188823955934649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10183807683459215970623099 15275711525188823955934649)
    ·
      refine ⟨11456783643891617966950987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15275711525188823955934649 11456783643891617966950987)
      ·
        refine ⟨17185175465837426950426481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11456783643891617966950987 17185175465837426950426481)
        ·
          refine ⟨12888881599378070212819861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17185175465837426950426481 12888881599378070212819861)
          ·
            refine ⟨604166324970847041225931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12888881599378070212819861 604166324970847041225931)
            ·
              refine ⟨906249487456270561838897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604166324970847041225931 906249487456270561838897)
              ·
                refine ⟨679687115592202921379173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906249487456270561838897 679687115592202921379173)
                ·
                  refine ⟨127441334173538047758595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679687115592202921379173 127441334173538047758595)
                  ·
                    rfl

theorem cell20_279215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_279215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279215 prefixEnd_279215 := by exact prefixLift 279215
  have htrace : WordTrace (prefixWord ++ tailWord_279215) baseStart_279215 baseEnd_279215 := by
    simpa [prefixWord, tailWord_279215, baseEnd_279215] using wordTrace_append hprefix tailTrace_279215
  have hstable : (prefixWord ++ tailWord_279215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279215).length < 2 ^ (prefixWord ++ tailWord_279215).sum := by decide
  have hdescent : baseEnd_279215 < baseStart_279215 := by decide
  rcases family_descends (prefixWord ++ tailWord_279215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279232 : List Nat := [2, 1, 1, 2, 4, 2, 1, 5, 2]
def baseStart_279232 : Nat := 118140960795 + 279232 * 2 ^ 59
def prefixEnd_279232 : Nat := 4983230072969 + 3 ^ 40 * 279232 * 2
def baseEnd_279232 : Nat := 127449093436761544191859

theorem tailTrace_279232 : CollatzResearch.WordTrace tailWord_279232 prefixEnd_279232 127449093436761544191859 := by
  unfold tailWord_279232
  simp only [CollatzResearch.WordTrace]
  refine ⟨5092213862198813936995975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6789618482931751915994633 5092213862198813936995975)
  ·
    refine ⟨7638320793298220905493963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5092213862198813936995975 7638320793298220905493963)
    ·
      refine ⟨11457481189947331358240945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7638320793298220905493963 11457481189947331358240945)
      ·
        refine ⟨8593110892460498518680709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11457481189947331358240945 8593110892460498518680709)
        ·
          refine ⟨1611208292336343472252633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8593110892460498518680709 1611208292336343472252633)
          ·
            refine ⟨1208406219252257604189475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1611208292336343472252633 1208406219252257604189475)
            ·
              refine ⟨1812609328878386406284213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208406219252257604189475 1812609328878386406284213)
              ·
                refine ⟨169932124582348725589145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1812609328878386406284213 169932124582348725589145)
                ·
                  refine ⟨127449093436761544191859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169932124582348725589145 127449093436761544191859)
                  ·
                    rfl

theorem cell20_279232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_279232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279232 prefixEnd_279232 := by exact prefixLift 279232
  have htrace : WordTrace (prefixWord ++ tailWord_279232) baseStart_279232 baseEnd_279232 := by
    simpa [prefixWord, tailWord_279232, baseEnd_279232] using wordTrace_append hprefix tailTrace_279232
  have hstable : (prefixWord ++ tailWord_279232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279232).length < 2 ^ (prefixWord ++ tailWord_279232).sum := by decide
  have hdescent : baseEnd_279232 < baseStart_279232 := by decide
  rcases family_descends (prefixWord ++ tailWord_279232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279238 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_279238 : Nat := 118140960795 + 279238 * 2 ^ 59
def prefixEnd_279238 : Nat := 4983230072969 + 3 ^ 40 * 279238 * 2
def baseEnd_279238 : Nat := 127451832000252189991835

theorem tailTrace_279238 : CollatzResearch.WordTrace tailWord_279238 prefixEnd_279238 127451832000252189991835 := by
  unfold tailWord_279238
  simp only [CollatzResearch.WordTrace]
  refine ⟨318270205074246590584699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6789764374917260599140245 318270205074246590584699)
  ·
    refine ⟨477405307611369885877049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 318270205074246590584699 477405307611369885877049)
    ·
      refine ⟨358053980708527414407787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 477405307611369885877049 358053980708527414407787)
      ·
        refine ⟨537080971062791121611681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358053980708527414407787 537080971062791121611681)
        ·
          refine ⟨402810728297093341208761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 537080971062791121611681 402810728297093341208761)
          ·
            refine ⟨302108046222820005906571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402810728297093341208761 302108046222820005906571)
            ·
              refine ⟨453162069334230008859857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302108046222820005906571 453162069334230008859857)
              ·
                refine ⟨339871552000672506644893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453162069334230008859857 339871552000672506644893)
                ·
                  refine ⟨127451832000252189991835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339871552000672506644893 127451832000252189991835)
                  ·
                    rfl

theorem cell20_279238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_279238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279238 prefixEnd_279238 := by exact prefixLift 279238
  have htrace : WordTrace (prefixWord ++ tailWord_279238) baseStart_279238 baseEnd_279238 := by
    simpa [prefixWord, tailWord_279238, baseEnd_279238] using wordTrace_append hprefix tailTrace_279238
  have hstable : (prefixWord ++ tailWord_279238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279238).length < 2 ^ (prefixWord ++ tailWord_279238).sum := by decide
  have hdescent : baseEnd_279238 < baseStart_279238 := by decide
  rcases family_descends (prefixWord ++ tailWord_279238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279246 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_279246 : Nat := 118140960795 + 279246 * 2 ^ 59
def prefixEnd_279246 : Nat := 4983230072969 + 3 ^ 40 * 279246 * 2
def baseEnd_279246 : Nat := 127455483418239717725135

theorem tailTrace_279246 : CollatzResearch.WordTrace tailWord_279246 prefixEnd_279246 127455483418239717725135 := by
  unfold tailWord_279246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273117293293363533125199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6789958897564605510001061 1273117293293363533125199)
  ·
    refine ⟨1909675939940045299687799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1273117293293363533125199 1909675939940045299687799)
    ·
      refine ⟨2864513909910067949531699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1909675939940045299687799 2864513909910067949531699)
      ·
        refine ⟨4296770864865101924297549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2864513909910067949531699 4296770864865101924297549)
        ·
          refine ⟨1611289074324413221611581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4296770864865101924297549 1611289074324413221611581)
          ·
            refine ⟨604233402871654958104343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1611289074324413221611581 604233402871654958104343)
            ·
              refine ⟨906350104307482437156515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604233402871654958104343 906350104307482437156515)
              ·
                refine ⟨1359525156461223655734773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906350104307482437156515 1359525156461223655734773)
                ·
                  refine ⟨127455483418239717725135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1359525156461223655734773 127455483418239717725135)
                  ·
                    rfl

theorem cell20_279246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_279246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279246 prefixEnd_279246 := by exact prefixLift 279246
  have htrace : WordTrace (prefixWord ++ tailWord_279246) baseStart_279246 baseEnd_279246 := by
    simpa [prefixWord, tailWord_279246, baseEnd_279246] using wordTrace_append hprefix tailTrace_279246
  have hstable : (prefixWord ++ tailWord_279246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279246).length < 2 ^ (prefixWord ++ tailWord_279246).sum := by decide
  have hdescent : baseEnd_279246 < baseStart_279246 := by decide
  rcases family_descends (prefixWord ++ tailWord_279246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279263 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 3]
def baseStart_279263 : Nat := 118140960795 + 279263 * 2 ^ 59
def prefixEnd_279263 : Nat := 4983230072969 + 3 ^ 40 * 279263 * 2
def baseEnd_279263 : Nat := 127463242681463214158399

theorem tailTrace_279263 : CollatzResearch.WordTrace tailWord_279263 prefixEnd_279263 127463242681463214158399 := by
  unfold tailWord_279263
  simp only [CollatzResearch.WordTrace]
  refine ⟨10185558387285320168370443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6790372258190213445580295 10185558387285320168370443)
  ·
    refine ⟨15278337580927980252555665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10185558387285320168370443 15278337580927980252555665)
    ·
      refine ⟨11458753185695985189416749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15278337580927980252555665 11458753185695985189416749)
      ·
        refine ⟨4297032444635994446031281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11458753185695985189416749 4297032444635994446031281)
        ·
          refine ⟨3222774333476995834523461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4297032444635994446031281 3222774333476995834523461)
          ·
            refine ⟨604270187526936718973149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3222774333476995834523461 604270187526936718973149)
            ·
              refine ⟨226601320322601269614931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 604270187526936718973149 226601320322601269614931)
              ·
                refine ⟨339901980483901904422397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226601320322601269614931 339901980483901904422397)
                ·
                  refine ⟨127463242681463214158399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339901980483901904422397 127463242681463214158399)
                  ·
                    rfl

theorem cell20_279263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 3].length) (baseStart_279263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279263 prefixEnd_279263 := by exact prefixLift 279263
  have htrace : WordTrace (prefixWord ++ tailWord_279263) baseStart_279263 baseEnd_279263 := by
    simpa [prefixWord, tailWord_279263, baseEnd_279263] using wordTrace_append hprefix tailTrace_279263
  have hstable : (prefixWord ++ tailWord_279263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279263).length < 2 ^ (prefixWord ++ tailWord_279263).sum := by decide
  have hdescent : baseEnd_279263 < baseStart_279263 := by decide
  rcases family_descends (prefixWord ++ tailWord_279263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279305 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_279305 : Nat := 118140960795 + 279305 * 2 ^ 59
def prefixEnd_279305 : Nat := 4983230072969 + 3 ^ 40 * 279305 * 2
def baseEnd_279305 : Nat := 127482412625897734758227

theorem tailTrace_279305 : CollatzResearch.WordTrace tailWord_279305 prefixEnd_279305 127482412625897734758227 := by
  unfold tailWord_279305
  simp only [CollatzResearch.WordTrace]
  refine ⟨10187090253133161341399369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6791393502088774227599579 10187090253133161341399369)
  ·
    refine ⟨7640317689849871006049527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10187090253133161341399369 7640317689849871006049527)
    ·
      refine ⟨11460476534774806509074291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7640317689849871006049527 11460476534774806509074291)
      ·
        refine ⟨17190714802162209763611437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11460476534774806509074291 17190714802162209763611437)
        ·
          refine ⟨6446518050810828661354289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17190714802162209763611437 6446518050810828661354289)
          ·
            refine ⟨4834888538108121496015717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6446518050810828661354289 4834888538108121496015717)
            ·
              refine ⟨906541600895272780502947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4834888538108121496015717 906541600895272780502947)
              ·
                refine ⟨1359812401342909170754421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906541600895272780502947 1359812401342909170754421)
                ·
                  refine ⟨127482412625897734758227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1359812401342909170754421 127482412625897734758227)
                  ·
                    rfl

theorem cell20_279305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_279305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279305 prefixEnd_279305 := by exact prefixLift 279305
  have htrace : WordTrace (prefixWord ++ tailWord_279305) baseStart_279305 baseEnd_279305 := by
    simpa [prefixWord, tailWord_279305, baseEnd_279305] using wordTrace_append hprefix tailTrace_279305
  have hstable : (prefixWord ++ tailWord_279305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279305).length < 2 ^ (prefixWord ++ tailWord_279305).sum := by decide
  have hdescent : baseEnd_279305 < baseStart_279305 := by decide
  rcases family_descends (prefixWord ++ tailWord_279305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279314 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 3]
def baseStart_279314 : Nat := 118140960795 + 279314 * 2 ^ 59
def prefixEnd_279314 : Nat := 4983230072969 + 3 ^ 40 * 279314 * 2
def baseEnd_279314 : Nat := 127486520471133703458191

theorem tailTrace_279314 : CollatzResearch.WordTrace tailWord_279314 prefixEnd_279314 127486520471133703458191 := by
  unfold tailWord_279314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546854627525138969619249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6791612340067037252317997 2546854627525138969619249)
  ·
    refine ⟨1910140970643854227214437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2546854627525138969619249 1910140970643854227214437)
    ·
      refine ⟨358151431995722667602707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1910140970643854227214437 358151431995722667602707)
      ·
        refine ⟨537227147993584001404061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358151431995722667602707 537227147993584001404061)
        ·
          refine ⟨201460180497594000526523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 537227147993584001404061 201460180497594000526523)
          ·
            refine ⟨302190270746391000789785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201460180497594000526523 302190270746391000789785)
            ·
              refine ⟨226642703059793250592339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302190270746391000789785 226642703059793250592339)
              ·
                refine ⟨339964054589689875888509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226642703059793250592339 339964054589689875888509)
                ·
                  refine ⟨127486520471133703458191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339964054589689875888509 127486520471133703458191)
                  ·
                    rfl

theorem cell20_279314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_279314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279314 prefixEnd_279314 := by exact prefixLift 279314
  have htrace : WordTrace (prefixWord ++ tailWord_279314) baseStart_279314 baseEnd_279314 := by
    simpa [prefixWord, tailWord_279314, baseEnd_279314] using wordTrace_append hprefix tailTrace_279314
  have hstable : (prefixWord ++ tailWord_279314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279314).length < 2 ^ (prefixWord ++ tailWord_279314).sum := by decide
  have hdescent : baseEnd_279314 < baseStart_279314 := by decide
  rcases family_descends (prefixWord ++ tailWord_279314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279322 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_279322 : Nat := 118140960795 + 279322 * 2 ^ 59
def prefixEnd_279322 : Nat := 4983230072969 + 3 ^ 40 * 279322 * 2
def baseEnd_279322 : Nat := 127490171889121231191491

theorem tailTrace_279322 : CollatzResearch.WordTrace tailWord_279322 prefixEnd_279322 127490171889121231191491 := by
  unfold tailWord_279322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546927573517893311192055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6791806862714382163178813 2546927573517893311192055)
  ·
    refine ⟨3820391360276839966788083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2546927573517893311192055 3820391360276839966788083)
    ·
      refine ⟨5730587040415259950182125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3820391360276839966788083 5730587040415259950182125)
      ·
        refine ⟨2148970140155722481318297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5730587040415259950182125 2148970140155722481318297)
        ·
          refine ⟨1611727605116791860988723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2148970140155722481318297 1611727605116791860988723)
          ·
            refine ⟨2417591407675187791483085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611727605116791860988723 2417591407675187791483085)
            ·
              refine ⟨906596777878195421806157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2417591407675187791483085 906596777878195421806157)
              ·
                refine ⟨339973791704323283177309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 906596777878195421806157 339973791704323283177309)
                ·
                  refine ⟨127490171889121231191491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339973791704323283177309 127490171889121231191491)
                  ·
                    rfl

theorem cell20_279322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_279322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279322 prefixEnd_279322 := by exact prefixLift 279322
  have htrace : WordTrace (prefixWord ++ tailWord_279322) baseStart_279322 baseEnd_279322 := by
    simpa [prefixWord, tailWord_279322, baseEnd_279322] using wordTrace_append hprefix tailTrace_279322
  have hstable : (prefixWord ++ tailWord_279322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279322).length < 2 ^ (prefixWord ++ tailWord_279322).sum := by decide
  have hdescent : baseEnd_279322 < baseStart_279322 := by decide
  rcases family_descends (prefixWord ++ tailWord_279322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279336 : List Nat := [2, 1, 5, 1, 1, 1, 1, 8]
def baseStart_279336 : Nat := 118140960795 + 279336 * 2 ^ 59
def prefixEnd_279336 : Nat := 4983230072969 + 3 ^ 40 * 279336 * 2
def baseEnd_279336 : Nat := 42498853956866468241589

theorem tailTrace_279336 : CollatzResearch.WordTrace tailWord_279336 prefixEnd_279336 42498853956866468241589 := by
  unfold tailWord_279336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5094110458010426817888931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6792147277347235757185241 5094110458010426817888931)
  ·
    refine ⟨7641165687015640226833397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5094110458010426817888931 7641165687015640226833397)
    ·
      refine ⟨716359283157716271265631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7641165687015640226833397 716359283157716271265631)
      ·
        refine ⟨1074538924736574406898447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 716359283157716271265631 1074538924736574406898447)
        ·
          refine ⟨1611808387104861610347671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1074538924736574406898447 1611808387104861610347671)
          ·
            refine ⟨2417712580657292415521507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611808387104861610347671 2417712580657292415521507)
            ·
              refine ⟨3626568870985938623282261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417712580657292415521507 3626568870985938623282261)
              ·
                refine ⟨42498853956866468241589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3626568870985938623282261 42498853956866468241589)
                ·
                  rfl

theorem cell20_279336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_279336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279336 prefixEnd_279336 := by exact prefixLift 279336
  have htrace : WordTrace (prefixWord ++ tailWord_279336) baseStart_279336 baseEnd_279336 := by
    simpa [prefixWord, tailWord_279336, baseEnd_279336] using wordTrace_append hprefix tailTrace_279336
  have hstable : (prefixWord ++ tailWord_279336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279336).length < 2 ^ (prefixWord ++ tailWord_279336).sum := by decide
  have hdescent : baseEnd_279336 < baseStart_279336 := by decide
  rcases family_descends (prefixWord ++ tailWord_279336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279346 : List Nat := [3, 2, 1, 1, 3, 1, 2, 5, 2]
def baseStart_279346 : Nat := 118140960795 + 279346 * 2 ^ 59
def prefixEnd_279346 : Nat := 4983230072969 + 3 ^ 40 * 279346 * 2
def baseEnd_279346 : Nat := 127501126143083814391393

theorem tailTrace_279346 : CollatzResearch.WordTrace tailWord_279346 prefixEnd_279346 127501126143083814391393 := by
  unfold tailWord_279346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547146411496156335910473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6792390430656416895761261 2547146411496156335910473)
  ·
    refine ⟨1910359808622117251932855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2547146411496156335910473 1910359808622117251932855)
    ·
      refine ⟨2865539712933175877899283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1910359808622117251932855 2865539712933175877899283)
      ·
        refine ⟨4298309569399763816848925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2865539712933175877899283 4298309569399763816848925)
        ·
          refine ⟨1611866088524911431318347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4298309569399763816848925 1611866088524911431318347)
          ·
            refine ⟨2417799132787367146977521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611866088524911431318347 2417799132787367146977521)
            ·
              refine ⟨1813349349590525360233141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417799132787367146977521 1813349349590525360233141)
              ·
                refine ⟨170001501524111752521857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1813349349590525360233141 170001501524111752521857)
                ·
                  refine ⟨127501126143083814391393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170001501524111752521857 127501126143083814391393)
                  ·
                    rfl

theorem cell20_279346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_279346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279346 prefixEnd_279346 := by exact prefixLift 279346
  have htrace : WordTrace (prefixWord ++ tailWord_279346) baseStart_279346 baseEnd_279346 := by
    simpa [prefixWord, tailWord_279346, baseEnd_279346] using wordTrace_append hprefix tailTrace_279346
  have hstable : (prefixWord ++ tailWord_279346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279346).length < 2 ^ (prefixWord ++ tailWord_279346).sum := by decide
  have hdescent : baseEnd_279346 < baseStart_279346 := by decide
  rcases family_descends (prefixWord ++ tailWord_279346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279366 : List Nat := [6, 1, 1, 2, 3, 1, 1, 5]
def baseStart_279366 : Nat := 118140960795 + 279366 * 2 ^ 59
def prefixEnd_279366 : Nat := 4983230072969 + 3 ^ 40 * 279366 * 2
def baseEnd_279366 : Nat := 42503418229350877908215

theorem tailTrace_279366 : CollatzResearch.WordTrace tailWord_279366 prefixEnd_279366 42503418229350877908215 := by
  unfold tailWord_279366
  simp only [CollatzResearch.WordTrace]
  refine ⟨318416097059755273730311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6792876737274779172913301 318416097059755273730311)
  ·
    refine ⟨477624145589632910595467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 318416097059755273730311 477624145589632910595467)
    ·
      refine ⟨716436218384449365893201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477624145589632910595467 716436218384449365893201)
      ·
        refine ⟨537327163788337024419901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 716436218384449365893201 537327163788337024419901)
        ·
          refine ⟨201497686420626384157463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 537327163788337024419901 201497686420626384157463)
          ·
            refine ⟨302246529630939576236195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201497686420626384157463 302246529630939576236195)
            ·
              refine ⟨453369794446409364354293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302246529630939576236195 453369794446409364354293)
              ·
                refine ⟨42503418229350877908215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 453369794446409364354293 42503418229350877908215)
                ·
                  rfl

theorem cell20_279366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_279366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279366 prefixEnd_279366 := by exact prefixLift 279366
  have htrace : WordTrace (prefixWord ++ tailWord_279366) baseStart_279366 baseEnd_279366 := by
    simpa [prefixWord, tailWord_279366, baseEnd_279366] using wordTrace_append hprefix tailTrace_279366
  have hstable : (prefixWord ++ tailWord_279366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279366).length < 2 ^ (prefixWord ++ tailWord_279366).sum := by decide
  have hdescent : baseEnd_279366 < baseStart_279366 := by decide
  rcases family_descends (prefixWord ++ tailWord_279366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279477 : List Nat := [1, 3, 3, 2, 1, 1, 5, 2, 2]
def baseStart_279477 : Nat := 118140960795 + 279477 * 2 ^ 59
def prefixEnd_279477 : Nat := 4983230072969 + 3 ^ 40 * 279477 * 2
def baseEnd_279477 : Nat := 127560918112629581024191

theorem tailTrace_279477 : CollatzResearch.WordTrace tailWord_279477 prefixEnd_279477 127560918112629581024191 := by
  unfold tailWord_279477
  simp only [CollatzResearch.WordTrace]
  refine ⟨10193363608510034716660685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6795575739006689811107123 10193363608510034716660685)
  ·
    refine ⟨3822511353191263018747757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10193363608510034716660685 3822511353191263018747757)
    ·
      refine ⟨1433441757446723632030409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3822511353191263018747757 1433441757446723632030409)
      ·
        refine ⟨1075081318085042724022807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1433441757446723632030409 1075081318085042724022807)
        ·
          refine ⟨1612621977127564086034211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075081318085042724022807 1612621977127564086034211)
          ·
            refine ⟨2418932965691346129051317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612621977127564086034211 2418932965691346129051317)
            ·
              refine ⟨226774965533563699598561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2418932965691346129051317 226774965533563699598561)
              ·
                refine ⟨170081224150172774698921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226774965533563699598561 170081224150172774698921)
                ·
                  refine ⟨127560918112629581024191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170081224150172774698921 127560918112629581024191)
                  ·
                    rfl

theorem cell20_279477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_279477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279477 prefixEnd_279477 := by exact prefixLift 279477
  have htrace : WordTrace (prefixWord ++ tailWord_279477) baseStart_279477 baseEnd_279477 := by
    simpa [prefixWord, tailWord_279477, baseEnd_279477] using wordTrace_append hprefix tailTrace_279477
  have hstable : (prefixWord ++ tailWord_279477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279477).length < 2 ^ (prefixWord ++ tailWord_279477).sum := by decide
  have hdescent : baseEnd_279477 < baseStart_279477 := by decide
  rcases family_descends (prefixWord ++ tailWord_279477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279481 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 4]
def baseStart_279481 : Nat := 118140960795 + 279481 * 2 ^ 59
def prefixEnd_279481 : Nat := 4983230072969 + 3 ^ 40 * 279481 * 2
def baseEnd_279481 : Nat := 127562743821623344890841

theorem tailTrace_279481 : CollatzResearch.WordTrace tailWord_279481 prefixEnd_279481 127562743821623344890841 := by
  unfold tailWord_279481
  simp only [CollatzResearch.WordTrace]
  refine ⟨10193509500495543399806297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6795673000330362266537531 10193509500495543399806297)
  ·
    refine ⟨7645132125371657549854723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10193509500495543399806297 7645132125371657549854723)
    ·
      refine ⟨11467698188057486324782085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7645132125371657549854723 11467698188057486324782085)
      ·
        refine ⟨2150193410260778685896641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11467698188057486324782085 2150193410260778685896641)
        ·
          refine ⟨1612645057695584014422481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2150193410260778685896641 1612645057695584014422481)
          ·
            refine ⟨1209483793271688010816861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1612645057695584014422481 1209483793271688010816861)
            ·
              refine ⟨453556422476883004056323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1209483793271688010816861 453556422476883004056323)
              ·
                refine ⟨680334633715324506084485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453556422476883004056323 680334633715324506084485)
                ·
                  refine ⟨127562743821623344890841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680334633715324506084485 127562743821623344890841)
                  ·
                    rfl

theorem cell20_279481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_279481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279481 prefixEnd_279481 := by exact prefixLift 279481
  have htrace : WordTrace (prefixWord ++ tailWord_279481) baseStart_279481 baseEnd_279481 := by
    simpa [prefixWord, tailWord_279481, baseEnd_279481] using wordTrace_append hprefix tailTrace_279481
  have hstable : (prefixWord ++ tailWord_279481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279481).length < 2 ^ (prefixWord ++ tailWord_279481).sum := by decide
  have hdescent : baseEnd_279481 < baseStart_279481 := by decide
  rcases family_descends (prefixWord ++ tailWord_279481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279488 : List Nat := [2, 1, 1, 2, 3, 4, 2, 5]
def baseStart_279488 : Nat := 118140960795 + 279488 * 2 ^ 59
def prefixEnd_279488 : Nat := 4983230072969 + 3 ^ 40 * 279488 * 2
def baseEnd_279488 : Nat := 42521979604120810552493

theorem tailTrace_279488 : CollatzResearch.WordTrace tailWord_279488 prefixEnd_279488 42521979604120810552493 := by
  unfold tailWord_279488
  simp only [CollatzResearch.WordTrace]
  refine ⟨5096882405735091797655559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6795843207646789063540745 5096882405735091797655559)
  ·
    refine ⟨7645323608602637696483339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5096882405735091797655559 7645323608602637696483339)
    ·
      refine ⟨11467985412903956544725009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7645323608602637696483339 11467985412903956544725009)
      ·
        refine ⟨8600989059677967408543757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11467985412903956544725009 8600989059677967408543757)
        ·
          refine ⟨3225370897379237778203909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8600989059677967408543757 3225370897379237778203909)
          ·
            refine ⟨604757043258607083413233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3225370897379237778203909 604757043258607083413233)
            ·
              refine ⟨453567782443955312559925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604757043258607083413233 453567782443955312559925)
              ·
                refine ⟨42521979604120810552493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 453567782443955312559925 42521979604120810552493)
                ·
                  rfl

theorem cell20_279488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_279488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279488 prefixEnd_279488 := by exact prefixLift 279488
  have htrace : WordTrace (prefixWord ++ tailWord_279488) baseStart_279488 baseEnd_279488 := by
    simpa [prefixWord, tailWord_279488, baseEnd_279488] using wordTrace_append hprefix tailTrace_279488
  have hstable : (prefixWord ++ tailWord_279488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279488).length < 2 ^ (prefixWord ++ tailWord_279488).sum := by decide
  have hdescent : baseEnd_279488 < baseStart_279488 := by decide
  rcases family_descends (prefixWord ++ tailWord_279488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279578 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_279578 : Nat := 118140960795 + 279578 * 2 ^ 59
def prefixEnd_279578 : Nat := 4983230072969 + 3 ^ 40 * 279578 * 2
def baseEnd_279578 : Nat := 127607017264722118657111

theorem tailTrace_279578 : CollatzResearch.WordTrace tailWord_279578 prefixEnd_279578 127607017264722118657111 := by
  unfold tailWord_279578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549261845286032241521847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6798031587429419310724925 2549261845286032241521847)
  ·
    refine ⟨3823892767929048362282771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2549261845286032241521847 3823892767929048362282771)
    ·
      refine ⟨5735839151893572543424157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3823892767929048362282771 5735839151893572543424157)
      ·
        refine ⟨2150939681960089703784059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5735839151893572543424157 2150939681960089703784059)
        ·
          refine ⟨3226409522940134555676089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2150939681960089703784059 3226409522940134555676089)
          ·
            refine ⟨2419807142205100916757067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3226409522940134555676089 2419807142205100916757067)
            ·
              refine ⟨3629710713307651375135601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2419807142205100916757067 3629710713307651375135601)
              ·
                refine ⟨2722283034980738531351701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3629710713307651375135601 2722283034980738531351701)
                ·
                  refine ⟨127607017264722118657111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2722283034980738531351701 127607017264722118657111)
                  ·
                    rfl

theorem cell20_279578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_279578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279578 prefixEnd_279578 := by exact prefixLift 279578
  have htrace : WordTrace (prefixWord ++ tailWord_279578) baseStart_279578 baseEnd_279578 := by
    simpa [prefixWord, tailWord_279578, baseEnd_279578] using wordTrace_append hprefix tailTrace_279578
  have hstable : (prefixWord ++ tailWord_279578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279578).length < 2 ^ (prefixWord ++ tailWord_279578).sum := by decide
  have hdescent : baseEnd_279578 < baseStart_279578 := by decide
  rcases family_descends (prefixWord ++ tailWord_279578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279584 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 3]
def baseStart_279584 : Nat := 118140960795 + 279584 * 2 ^ 59
def prefixEnd_279584 : Nat := 4983230072969 + 3 ^ 40 * 279584 * 2
def baseEnd_279584 : Nat := 127609755828212764457087

theorem tailTrace_279584 : CollatzResearch.WordTrace tailWord_279584 prefixEnd_279584 127609755828212764457087 := by
  unfold tailWord_279584
  simp only [CollatzResearch.WordTrace]
  refine ⟨5098633109561195995402903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6798177479414927993870537 5098633109561195995402903)
  ·
    refine ⟨7647949664341793993104355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5098633109561195995402903 7647949664341793993104355)
    ·
      refine ⟨11471924496512690989656533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7647949664341793993104355 11471924496512690989656533)
      ·
        refine ⟨268873230387016195070075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 11471924496512690989656533 268873230387016195070075)
        ·
          refine ⟨403309845580524292605113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268873230387016195070075 403309845580524292605113)
          ·
            refine ⟨302482384185393219453835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403309845580524292605113 302482384185393219453835)
            ·
              refine ⟨453723576278089829180753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302482384185393219453835 453723576278089829180753)
              ·
                refine ⟨340292682208567371885565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453723576278089829180753 340292682208567371885565)
                ·
                  refine ⟨127609755828212764457087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340292682208567371885565 127609755828212764457087)
                  ·
                    rfl

theorem cell20_279584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_279584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279584 prefixEnd_279584 := by exact prefixLift 279584
  have htrace : WordTrace (prefixWord ++ tailWord_279584) baseStart_279584 baseEnd_279584 := by
    simpa [prefixWord, tailWord_279584, baseEnd_279584] using wordTrace_append hprefix tailTrace_279584
  have hstable : (prefixWord ++ tailWord_279584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279584).length < 2 ^ (prefixWord ++ tailWord_279584).sum := by decide
  have hdescent : baseEnd_279584 < baseStart_279584 := by decide
  rcases family_descends (prefixWord ++ tailWord_279584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279588 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_279588 : Nat := 118140960795 + 279588 * 2 ^ 59
def prefixEnd_279588 : Nat := 4983230072969 + 3 ^ 40 * 279588 * 2
def baseEnd_279588 : Nat := 127611581537206528323737

theorem tailTrace_279588 : CollatzResearch.WordTrace tailWord_279588 prefixEnd_279588 127611581537206528323737 := by
  unfold tailWord_279588
  simp only [CollatzResearch.WordTrace]
  refine ⟨5098706055553950336975709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6798274740738600449300945 5098706055553950336975709)
  ·
    refine ⟨1912014770832731376365891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5098706055553950336975709 1912014770832731376365891)
    ·
      refine ⟨2868022156249097064548837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1912014770832731376365891 2868022156249097064548837)
      ·
        refine ⟨537754154296705699602907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2868022156249097064548837 537754154296705699602907)
        ·
          refine ⟨806631231445058549404361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537754154296705699602907 806631231445058549404361)
          ·
            refine ⟨604973423583793912053271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806631231445058549404361 604973423583793912053271)
            ·
              refine ⟨907460135375690868079907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604973423583793912053271 907460135375690868079907)
              ·
                refine ⟨1361190203063536302119861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907460135375690868079907 1361190203063536302119861)
                ·
                  refine ⟨127611581537206528323737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1361190203063536302119861 127611581537206528323737)
                  ·
                    rfl

theorem cell20_279588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_279588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279588 prefixEnd_279588 := by exact prefixLift 279588
  have htrace : WordTrace (prefixWord ++ tailWord_279588) baseStart_279588 baseEnd_279588 := by
    simpa [prefixWord, tailWord_279588, baseEnd_279588] using wordTrace_append hprefix tailTrace_279588
  have hstable : (prefixWord ++ tailWord_279588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279588).length < 2 ^ (prefixWord ++ tailWord_279588).sum := by decide
  have hdescent : baseEnd_279588 < baseStart_279588 := by decide
  rcases family_descends (prefixWord ++ tailWord_279588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279591 : List Nat := [1, 1, 7, 1, 1, 1, 2, 4, 2]
def baseStart_279591 : Nat := 118140960795 + 279591 * 2 ^ 59
def prefixEnd_279591 : Nat := 4983230072969 + 3 ^ 40 * 279591 * 2
def baseEnd_279591 : Nat := 127612950818951851223725

theorem tailTrace_279591 : CollatzResearch.WordTrace tailWord_279591 prefixEnd_279591 127612950818951851223725 := by
  unfold tailWord_279591
  simp only [CollatzResearch.WordTrace]
  refine ⟨10197521530097032186310627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6798347686731354790873751 10197521530097032186310627)
  ·
    refine ⟨15296282295145548279465941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10197521530097032186310627 15296282295145548279465941)
    ·
      refine ⟨358506616292473787799983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15296282295145548279465941 358506616292473787799983)
      ·
        refine ⟨537759924438710681699975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358506616292473787799983 537759924438710681699975)
        ·
          refine ⟨806639886658066022549963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537759924438710681699975 806639886658066022549963)
          ·
            refine ⟨1209959829987099033824945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806639886658066022549963 1209959829987099033824945)
            ·
              refine ⟨907469872490324275368709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1209959829987099033824945 907469872490324275368709)
              ·
                refine ⟨170150601091935801631633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 907469872490324275368709 170150601091935801631633)
                ·
                  refine ⟨127612950818951851223725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170150601091935801631633 127612950818951851223725)
                  ·
                    rfl

theorem cell20_279591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 2].length) (baseStart_279591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279591 prefixEnd_279591 := by exact prefixLift 279591
  have htrace : WordTrace (prefixWord ++ tailWord_279591) baseStart_279591 baseEnd_279591 := by
    simpa [prefixWord, tailWord_279591, baseEnd_279591] using wordTrace_append hprefix tailTrace_279591
  have hstable : (prefixWord ++ tailWord_279591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279591).length < 2 ^ (prefixWord ++ tailWord_279591).sum := by decide
  have hdescent : baseEnd_279591 < baseStart_279591 := by decide
  rcases family_descends (prefixWord ++ tailWord_279591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279595 : List Nat := [1, 1, 1, 1, 2, 1, 5, 6, 2]
def baseStart_279595 : Nat := 118140960795 + 279595 * 2 ^ 59
def prefixEnd_279595 : Nat := 4983230072969 + 3 ^ 40 * 279595 * 2
def baseEnd_279595 : Nat := 127614776527945615090375

theorem tailTrace_279595 : CollatzResearch.WordTrace tailWord_279595 prefixEnd_279595 127614776527945615090375 := by
  unfold tailWord_279595
  simp only [CollatzResearch.WordTrace]
  refine ⟨10197667422082540869456239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6798444948055027246304159 10197667422082540869456239)
  ·
    refine ⟨15296501133123811304184359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10197667422082540869456239 15296501133123811304184359)
    ·
      refine ⟨22944751699685716956276539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15296501133123811304184359 22944751699685716956276539)
      ·
        refine ⟨34417127549528575434414809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22944751699685716956276539 34417127549528575434414809)
        ·
          refine ⟨25812845662146431575811107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34417127549528575434414809 25812845662146431575811107)
          ·
            refine ⟨38719268493219647363716661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25812845662146431575811107 38719268493219647363716661)
            ·
              refine ⟨3629931421239341940348437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38719268493219647363716661 3629931421239341940348437)
              ·
                refine ⟨170153035370594153453833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3629931421239341940348437 170153035370594153453833)
                ·
                  refine ⟨127614776527945615090375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170153035370594153453833 127614776527945615090375)
                  ·
                    rfl

theorem cell20_279595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 2].length) (baseStart_279595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279595 prefixEnd_279595 := by exact prefixLift 279595
  have htrace : WordTrace (prefixWord ++ tailWord_279595) baseStart_279595 baseEnd_279595 := by
    simpa [prefixWord, tailWord_279595, baseEnd_279595] using wordTrace_append hprefix tailTrace_279595
  have hstable : (prefixWord ++ tailWord_279595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279595).length < 2 ^ (prefixWord ++ tailWord_279595).sum := by decide
  have hdescent : baseEnd_279595 < baseStart_279595 := by decide
  rcases family_descends (prefixWord ++ tailWord_279595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279616 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_279616 : Nat := 118140960795 + 279616 * 2 ^ 59
def prefixEnd_279616 : Nat := 4983230072969 + 3 ^ 40 * 279616 * 2
def baseEnd_279616 : Nat := 127624361500162875390289

theorem tailTrace_279616 : CollatzResearch.WordTrace tailWord_279616 prefixEnd_279616 127624361500162875390289 := by
  unfold tailWord_279616
  simp only [CollatzResearch.WordTrace]
  refine ⟨5099216677503230727985351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6798955570004307637313801 5099216677503230727985351)
  ·
    refine ⟨7648825016254846091978027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5099216677503230727985351 7648825016254846091978027)
    ·
      refine ⟨11473237524382269137967041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7648825016254846091978027 11473237524382269137967041)
      ·
        refine ⟨8604928143286701853475281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11473237524382269137967041 8604928143286701853475281)
        ·
          refine ⟨6453696107465026390106461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8604928143286701853475281 6453696107465026390106461)
          ·
            refine ⟨2420136040299384896289923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6453696107465026390106461 2420136040299384896289923)
            ·
              refine ⟨3630204060449077344434885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420136040299384896289923 3630204060449077344434885)
              ·
                refine ⟨680663261334202002081541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3630204060449077344434885 680663261334202002081541)
                ·
                  refine ⟨127624361500162875390289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680663261334202002081541 127624361500162875390289)
                  ·
                    rfl

theorem cell20_279616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_279616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279616 prefixEnd_279616 := by exact prefixLift 279616
  have htrace : WordTrace (prefixWord ++ tailWord_279616) baseStart_279616 baseEnd_279616 := by
    simpa [prefixWord, tailWord_279616, baseEnd_279616] using wordTrace_append hprefix tailTrace_279616
  have hstable : (prefixWord ++ tailWord_279616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279616).length < 2 ^ (prefixWord ++ tailWord_279616).sum := by decide
  have hdescent : baseEnd_279616 < baseStart_279616 := by decide
  rcases family_descends (prefixWord ++ tailWord_279616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279629 : List Nat := [1, 6, 1, 1, 1, 2, 3, 3, 2]
def baseStart_279629 : Nat := 118140960795 + 279629 * 2 ^ 59
def prefixEnd_279629 : Nat := 4983230072969 + 3 ^ 40 * 279629 * 2
def baseEnd_279629 : Nat := 127630295054392607956903

theorem tailTrace_279629 : CollatzResearch.WordTrace tailWord_279629 prefixEnd_279629 127630295054392607956903 := by
  unfold tailWord_279629
  simp only [CollatzResearch.WordTrace]
  refine ⟨10198907503959364676193941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6799271669306243117462627 10198907503959364676193941)
  ·
    refine ⟨478073789248095219196591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10198907503959364676193941 478073789248095219196591)
    ·
      refine ⟨717110683872142828794887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 478073789248095219196591 717110683872142828794887)
      ·
        refine ⟨1075666025808214243192331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717110683872142828794887 1075666025808214243192331)
        ·
          refine ⟨1613499038712321364788497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075666025808214243192331 1613499038712321364788497)
          ·
            refine ⟨1210124279034241023591373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1613499038712321364788497 1210124279034241023591373)
            ·
              refine ⟨453796604637840383846765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1210124279034241023591373 453796604637840383846765)
              ·
                refine ⟨170173726739190143942537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 453796604637840383846765 170173726739190143942537)
                ·
                  refine ⟨127630295054392607956903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170173726739190143942537 127630295054392607956903)
                  ·
                    rfl

theorem cell20_279629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_279629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279629 prefixEnd_279629 := by exact prefixLift 279629
  have htrace : WordTrace (prefixWord ++ tailWord_279629) baseStart_279629 baseEnd_279629 := by
    simpa [prefixWord, tailWord_279629, baseEnd_279629] using wordTrace_append hprefix tailTrace_279629
  have hstable : (prefixWord ++ tailWord_279629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279629).length < 2 ^ (prefixWord ++ tailWord_279629).sum := by decide
  have hdescent : baseEnd_279629 < baseStart_279629 := by decide
  rcases family_descends (prefixWord ++ tailWord_279629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279646 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_279646 : Nat := 118140960795 + 279646 * 2 ^ 59
def prefixEnd_279646 : Nat := 4983230072969 + 3 ^ 40 * 279646 * 2
def baseEnd_279646 : Nat := 127638054317616104390167

theorem tailTrace_279646 : CollatzResearch.WordTrace tailWord_279646 prefixEnd_279646 127638054317616104390167 := by
  unfold tailWord_279646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1274940943112222072445349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6799685029931851053041861 1274940943112222072445349)
  ·
    refine ⟨239051426833541638583503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1274940943112222072445349 239051426833541638583503)
    ·
      refine ⟨358577140250312457875255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239051426833541638583503 358577140250312457875255)
      ·
        refine ⟨537865710375468686812883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358577140250312457875255 537865710375468686812883)
        ·
          refine ⟨806798565563203030219325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537865710375468686812883 806798565563203030219325)
          ·
            refine ⟨302549462086201136332247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 806798565563203030219325 302549462086201136332247)
            ·
              refine ⟨453824193129301704498371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302549462086201136332247 453824193129301704498371)
              ·
                refine ⟨680736289693952556747557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453824193129301704498371 680736289693952556747557)
                ·
                  refine ⟨127638054317616104390167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680736289693952556747557 127638054317616104390167)
                  ·
                    rfl

theorem cell20_279646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_279646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279646 prefixEnd_279646 := by exact prefixLift 279646
  have htrace : WordTrace (prefixWord ++ tailWord_279646) baseStart_279646 baseEnd_279646 := by
    simpa [prefixWord, tailWord_279646, baseEnd_279646] using wordTrace_append hprefix tailTrace_279646
  have hstable : (prefixWord ++ tailWord_279646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279646).length < 2 ^ (prefixWord ++ tailWord_279646).sum := by decide
  have hdescent : baseEnd_279646 < baseStart_279646 := by decide
  rcases family_descends (prefixWord ++ tailWord_279646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279647 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 3]
def baseStart_279647 : Nat := 118140960795 + 279647 * 2 ^ 59
def prefixEnd_279647 : Nat := 4983230072969 + 3 ^ 40 * 279647 * 2
def baseEnd_279647 : Nat := 127638510744864545356829

theorem tailTrace_279647 : CollatzResearch.WordTrace tailWord_279647 prefixEnd_279647 127638510744864545356829 := by
  unfold tailWord_279647
  simp only [CollatzResearch.WordTrace]
  refine ⟨10199564017894153750349195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6799709345262769166899463 10199564017894153750349195)
  ·
    refine ⟨15299346026841230625523793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10199564017894153750349195 15299346026841230625523793)
    ·
      refine ⟨11474509520130922969142845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15299346026841230625523793 11474509520130922969142845)
      ·
        refine ⟨4302941070049096113428567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11474509520130922969142845 4302941070049096113428567)
        ·
          refine ⟨6454411605073644170142851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4302941070049096113428567 6454411605073644170142851)
          ·
            refine ⟨9681617407610466255214277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6454411605073644170142851 9681617407610466255214277)
            ·
              refine ⟨1815303263926962422852677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9681617407610466255214277 1815303263926962422852677)
              ·
                refine ⟨340369361986305454284877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1815303263926962422852677 340369361986305454284877)
                ·
                  refine ⟨127638510744864545356829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340369361986305454284877 127638510744864545356829)
                  ·
                    rfl

theorem cell20_279647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 3].length) (baseStart_279647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279647 prefixEnd_279647 := by exact prefixLift 279647
  have htrace : WordTrace (prefixWord ++ tailWord_279647) baseStart_279647 baseEnd_279647 := by
    simpa [prefixWord, tailWord_279647, baseEnd_279647] using wordTrace_append hprefix tailTrace_279647
  have hstable : (prefixWord ++ tailWord_279647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279647).length < 2 ^ (prefixWord ++ tailWord_279647).sum := by decide
  have hdescent : baseEnd_279647 < baseStart_279647 := by decide
  rcases family_descends (prefixWord ++ tailWord_279647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279650 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_279650 : Nat := 118140960795 + 279650 * 2 ^ 59
def prefixEnd_279650 : Nat := 4983230072969 + 3 ^ 40 * 279650 * 2
def baseEnd_279650 : Nat := 127639880026609868256817

theorem tailTrace_279650 : CollatzResearch.WordTrace tailWord_279650 prefixEnd_279650 127639880026609868256817 := by
  unfold tailWord_279650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549918359220821315677101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6799782291255523508472269 2549918359220821315677101)
  ·
    refine ⟨956219384707807993378913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2549918359220821315677101 956219384707807993378913)
    ·
      refine ⟨717164538530855995034185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 956219384707807993378913 717164538530855995034185)
      ·
        refine ⟨537873403898141996275639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 717164538530855995034185 537873403898141996275639)
        ·
          refine ⟨806810105847212994413459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537873403898141996275639 806810105847212994413459)
          ·
            refine ⟨1210215158770819491620189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806810105847212994413459 1210215158770819491620189)
            ·
              refine ⟨453830684539057309357571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1210215158770819491620189 453830684539057309357571)
              ·
                refine ⟨680746026808585964036357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453830684539057309357571 680746026808585964036357)
                ·
                  refine ⟨127639880026609868256817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680746026808585964036357 127639880026609868256817)
                  ·
                    rfl

theorem cell20_279650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_279650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279650 prefixEnd_279650 := by exact prefixLift 279650
  have htrace : WordTrace (prefixWord ++ tailWord_279650) baseStart_279650 baseEnd_279650 := by
    simpa [prefixWord, tailWord_279650, baseEnd_279650] using wordTrace_append hprefix tailTrace_279650
  have hstable : (prefixWord ++ tailWord_279650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279650).length < 2 ^ (prefixWord ++ tailWord_279650).sum := by decide
  have hdescent : baseEnd_279650 < baseStart_279650 := by decide
  rcases family_descends (prefixWord ++ tailWord_279650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279716 : List Nat := [2, 3, 1, 2, 3, 1, 3, 5]
def baseStart_279716 : Nat := 118140960795 + 279716 * 2 ^ 59
def prefixEnd_279716 : Nat := 4983230072969 + 3 ^ 40 * 279716 * 2
def baseEnd_279716 : Nat := 42556668075002324018849

theorem tailTrace_279716 : CollatzResearch.WordTrace tailWord_279716 prefixEnd_279716 42556668075002324018849 := by
  unfold tailWord_279716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5101040327322089267305501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6801387103096119023074001 5101040327322089267305501)
  ·
    refine ⟨1912890122745783475239563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5101040327322089267305501 1912890122745783475239563)
    ·
      refine ⟨2869335184118675212859345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1912890122745783475239563 2869335184118675212859345)
      ·
        refine ⟨2152001388089006409644509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2869335184118675212859345 2152001388089006409644509)
        ·
          refine ⟨807000520533377403616691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2152001388089006409644509 807000520533377403616691)
          ·
            refine ⟨1210500780800066105425037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807000520533377403616691 1210500780800066105425037)
            ·
              refine ⟨453937792800024789534389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1210500780800066105425037 453937792800024789534389)
              ·
                refine ⟨42556668075002324018849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 453937792800024789534389 42556668075002324018849)
                ·
                  rfl

theorem cell20_279716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_279716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279716 prefixEnd_279716 := by exact prefixLift 279716
  have htrace : WordTrace (prefixWord ++ tailWord_279716) baseStart_279716 baseEnd_279716 := by
    simpa [prefixWord, tailWord_279716, baseEnd_279716] using wordTrace_append hprefix tailTrace_279716
  have hstable : (prefixWord ++ tailWord_279716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279716).length < 2 ^ (prefixWord ++ tailWord_279716).sum := by decide
  have hdescent : baseEnd_279716 < baseStart_279716 := by decide
  rcases family_descends (prefixWord ++ tailWord_279716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279730 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_279730 : Nat := 118140960795 + 279730 * 2 ^ 59
def prefixEnd_279730 : Nat := 4983230072969 + 3 ^ 40 * 279730 * 2
def baseEnd_279730 : Nat := 127676394206485145589823

theorem tailTrace_279730 : CollatzResearch.WordTrace tailWord_279730 prefixEnd_279730 127676394206485145589823 := by
  unfold tailWord_279730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550647819148364731405161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6801727517728972617080429 2550647819148364731405161)
  ·
    refine ⟨1912985864361273548553871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2550647819148364731405161 1912985864361273548553871)
    ·
      refine ⟨2869478796541910322830807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1912985864361273548553871 2869478796541910322830807)
      ·
        refine ⟨4304218194812865484246211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869478796541910322830807 4304218194812865484246211)
        ·
          refine ⟨6456327292219298226369317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304218194812865484246211 6456327292219298226369317)
          ·
            refine ⟨1210561367291118417444247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6456327292219298226369317 1210561367291118417444247)
            ·
              refine ⟨1815842050936677626166371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210561367291118417444247 1815842050936677626166371)
              ·
                refine ⟨2723763076405016439249557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815842050936677626166371 2723763076405016439249557)
                ·
                  refine ⟨127676394206485145589823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2723763076405016439249557 127676394206485145589823)
                  ·
                    rfl

theorem cell20_279730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_279730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279730 prefixEnd_279730 := by exact prefixLift 279730
  have htrace : WordTrace (prefixWord ++ tailWord_279730) baseStart_279730 baseEnd_279730 := by
    simpa [prefixWord, tailWord_279730, baseEnd_279730] using wordTrace_append hprefix tailTrace_279730
  have hstable : (prefixWord ++ tailWord_279730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279730).length < 2 ^ (prefixWord ++ tailWord_279730).sum := by decide
  have hdescent : baseEnd_279730 < baseStart_279730 := by decide
  rcases family_descends (prefixWord ++ tailWord_279730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279826 : List Nat := [3, 2, 4, 2, 1, 1, 2, 5]
def baseStart_279826 : Nat := 118140960795 + 279826 * 2 ^ 59
def prefixEnd_279826 : Nat := 4983230072969 + 3 ^ 40 * 279826 * 2
def baseEnd_279826 : Nat := 42573403740778492796477

theorem tailTrace_279826 : CollatzResearch.WordTrace tailWord_279826 prefixEnd_279826 42573403740778492796477 := by
  unfold tailWord_279826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2551523171061416830278833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6804061789497111547410221 2551523171061416830278833)
  ·
    refine ⟨1913642378296062622709125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2551523171061416830278833 1913642378296062622709125)
    ·
      refine ⟨358807945930511741757961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1913642378296062622709125 358807945930511741757961)
      ·
        refine ⟨269105959447883806318471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358807945930511741757961 269105959447883806318471)
        ·
          refine ⟨403658939171825709477707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269105959447883806318471 403658939171825709477707)
          ·
            refine ⟨605488408757738564216561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403658939171825709477707 605488408757738564216561)
            ·
              refine ⟨454116306568303923162421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605488408757738564216561 454116306568303923162421)
              ·
                refine ⟨42573403740778492796477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 454116306568303923162421 42573403740778492796477)
                ·
                  rfl

theorem cell20_279826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_279826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279826 prefixEnd_279826 := by exact prefixLift 279826
  have htrace : WordTrace (prefixWord ++ tailWord_279826) baseStart_279826 baseEnd_279826 := by
    simpa [prefixWord, tailWord_279826, baseEnd_279826] using wordTrace_append hprefix tailTrace_279826
  have hstable : (prefixWord ++ tailWord_279826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279826).length < 2 ^ (prefixWord ++ tailWord_279826).sum := by decide
  have hdescent : baseEnd_279826 < baseStart_279826 := by decide
  rcases family_descends (prefixWord ++ tailWord_279826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279844 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_279844 : Nat := 118140960795 + 279844 * 2 ^ 59
def prefixEnd_279844 : Nat := 4983230072969 + 3 ^ 40 * 279844 * 2
def baseEnd_279844 : Nat := 127728426912807415789357

theorem tailTrace_279844 : CollatzResearch.WordTrace tailWord_279844 prefixEnd_279844 127728426912807415789357 := by
  unfold tailWord_279844
  simp only [CollatzResearch.WordTrace]
  refine ⟨5103374599090228197635293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6804499465453637596847057 5103374599090228197635293)
  ·
    refine ⟨1913765474658835574113235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5103374599090228197635293 1913765474658835574113235)
    ·
      refine ⟨2870648211988253361169853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913765474658835574113235 2870648211988253361169853)
      ·
        refine ⟨1076493079495595010438695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2870648211988253361169853 1076493079495595010438695)
        ·
          refine ⟨1614739619243392515658043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1076493079495595010438695 1614739619243392515658043)
          ·
            refine ⟨2422109428865088773487065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614739619243392515658043 2422109428865088773487065)
            ·
              refine ⟨1816582071648816580115299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2422109428865088773487065 1816582071648816580115299)
              ·
                refine ⟨2724873107473224870172949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816582071648816580115299 2724873107473224870172949)
                ·
                  refine ⟨127728426912807415789357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2724873107473224870172949 127728426912807415789357)
                  ·
                    rfl

theorem cell20_279844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_279844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279844 prefixEnd_279844 := by exact prefixLift 279844
  have htrace : WordTrace (prefixWord ++ tailWord_279844) baseStart_279844 baseEnd_279844 := by
    simpa [prefixWord, tailWord_279844, baseEnd_279844] using wordTrace_append hprefix tailTrace_279844
  have hstable : (prefixWord ++ tailWord_279844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279844).length < 2 ^ (prefixWord ++ tailWord_279844).sum := by decide
  have hdescent : baseEnd_279844 < baseStart_279844 := by decide
  rcases family_descends (prefixWord ++ tailWord_279844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279916 : List Nat := [2, 2, 1, 1, 5, 2, 2, 3, 2]
def baseStart_279916 : Nat := 118140960795 + 279916 * 2 ^ 59
def prefixEnd_279916 : Nat := 4983230072969 + 3 ^ 40 * 279916 * 2
def baseEnd_279916 : Nat := 127761289674695165389063

theorem tailTrace_279916 : CollatzResearch.WordTrace tailWord_279916 prefixEnd_279916 127761289674695165389063 := by
  unfold tailWord_279916
  simp only [CollatzResearch.WordTrace]
  refine ⟨5104687626959806345945801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6806250169279741794594401 5104687626959806345945801)
  ·
    refine ⟨3828515720219854759459351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5104687626959806345945801 3828515720219854759459351)
    ·
      refine ⟨5742773580329782139189027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3828515720219854759459351 5742773580329782139189027)
      ·
        refine ⟨8614160370494673208783541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5742773580329782139189027 8614160370494673208783541)
        ·
          refine ⟨807577534733875613323457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8614160370494673208783541 807577534733875613323457)
          ·
            refine ⟨605683151050406709992593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 807577534733875613323457 605683151050406709992593)
            ·
              refine ⟨454262363287805032494445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605683151050406709992593 454262363287805032494445)
              ·
                refine ⟨170348386232926887185417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 454262363287805032494445 170348386232926887185417)
                ·
                  refine ⟨127761289674695165389063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170348386232926887185417 127761289674695165389063)
                  ·
                    rfl

theorem cell20_279916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_279916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279916 prefixEnd_279916 := by exact prefixLift 279916
  have htrace : WordTrace (prefixWord ++ tailWord_279916) baseStart_279916 baseEnd_279916 := by
    simpa [prefixWord, tailWord_279916, baseEnd_279916] using wordTrace_append hprefix tailTrace_279916
  have hstable : (prefixWord ++ tailWord_279916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279916).length < 2 ^ (prefixWord ++ tailWord_279916).sum := by decide
  have hdescent : baseEnd_279916 < baseStart_279916 := by decide
  rcases family_descends (prefixWord ++ tailWord_279916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
