import V185TrunkScan20Chunk032

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_201242 : List Nat := [3, 1, 1, 3, 1, 1, 4, 4, 2]
def baseStart_201242 : Nat := 118140960795 + 201242 * 2 ^ 59
def prefixEnd_201242 : Nat := 4983230072969 + 3 ^ 40 * 201242 * 2
def baseEnd_201242 : Nat := 91852332330850554177343

theorem tailTrace_201242 : CollatzResearch.WordTrace tailWord_201242 prefixEnd_201242 91852332330850554177343 := by
  unfold tailWord_201242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834974684235519560605495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4893265824628052161614653 1834974684235519560605495)
  ·
    refine ⟨2752462026353279340908243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1834974684235519560605495 2752462026353279340908243)
    ·
      refine ⟨4128693039529919011362365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2752462026353279340908243 4128693039529919011362365)
      ·
        refine ⟨1548259889823719629260887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4128693039529919011362365 1548259889823719629260887)
        ·
          refine ⟨2322389834735579443891331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548259889823719629260887 2322389834735579443891331)
          ·
            refine ⟨3483584752103369165836997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322389834735579443891331 3483584752103369165836997)
            ·
              refine ⟨653172141019381718594437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3483584752103369165836997 653172141019381718594437)
              ·
                refine ⟨122469776441134072236457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653172141019381718594437 122469776441134072236457)
                ·
                  refine ⟨91852332330850554177343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122469776441134072236457 91852332330850554177343)
                  ·
                    rfl

theorem cell20_201242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_201242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201242 prefixEnd_201242 := by exact prefixLift 201242
  have htrace : WordTrace (prefixWord ++ tailWord_201242) baseStart_201242 baseEnd_201242 := by
    simpa [prefixWord, tailWord_201242, baseEnd_201242] using wordTrace_append hprefix tailTrace_201242
  have hstable : (prefixWord ++ tailWord_201242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201242).length < 2 ^ (prefixWord ++ tailWord_201242).sum := by decide
  have hdescent : baseEnd_201242 < baseStart_201242 := by decide
  rcases family_descends (prefixWord ++ tailWord_201242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201280 : List Nat := [2, 1, 1, 2, 2, 2, 5, 3, 2]
def baseStart_201280 : Nat := 118140960795 + 201280 * 2 ^ 59
def prefixEnd_201280 : Nat := 4983230072969 + 3 ^ 40 * 201280 * 2
def baseEnd_201280 : Nat := 91869676566291310910521

theorem tailTrace_201280 : CollatzResearch.WordTrace tailWord_201280 prefixEnd_201280 91869676566291310910521 := by
  unfold tailWord_201280
  simp only [CollatzResearch.WordTrace]
  refine ⟨3670642355402205366152647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4894189807202940488203529 3670642355402205366152647)
  ·
    refine ⟨5505963533103308049228971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3670642355402205366152647 5505963533103308049228971)
    ·
      refine ⟨8258945299654962073843457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5505963533103308049228971 8258945299654962073843457)
      ·
        refine ⟨6194208974741221555382593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8258945299654962073843457 6194208974741221555382593)
        ·
          refine ⟨4645656731055916166536945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6194208974741221555382593 4645656731055916166536945)
          ·
            refine ⟨3484242548291937124902709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4645656731055916166536945 3484242548291937124902709)
            ·
              refine ⟨326647738902369105459629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3484242548291937124902709 326647738902369105459629)
              ·
                refine ⟨122492902088388414547361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326647738902369105459629 122492902088388414547361)
                ·
                  refine ⟨91869676566291310910521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122492902088388414547361 91869676566291310910521)
                  ·
                    rfl

theorem cell20_201280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_201280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201280 prefixEnd_201280 := by exact prefixLift 201280
  have htrace : WordTrace (prefixWord ++ tailWord_201280) baseStart_201280 baseEnd_201280 := by
    simpa [prefixWord, tailWord_201280, baseEnd_201280] using wordTrace_append hprefix tailTrace_201280
  have hstable : (prefixWord ++ tailWord_201280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201280).length < 2 ^ (prefixWord ++ tailWord_201280).sum := by decide
  have hdescent : baseEnd_201280 < baseStart_201280 := by decide
  rcases family_descends (prefixWord ++ tailWord_201280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201291 : List Nat := [1, 1, 1, 1, 3, 1, 12]
def baseStart_201291 : Nat := 118140960795 + 201291 * 2 ^ 59
def prefixEnd_201291 : Nat := 4983230072969 + 3 ^ 40 * 201291 * 2
def baseEnd_201291 : Nat := 10208299696224906838201

theorem tailTrace_201291 : CollatzResearch.WordTrace tailWord_201291 prefixEnd_201291 10208299696224906838201 := by
  unfold tailWord_201291
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341685913764559610955727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4894457275843039740637151 7341685913764559610955727)
  ·
    refine ⟨11012528870646839416433591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7341685913764559610955727 11012528870646839416433591)
    ·
      refine ⟨16518793305970259124650387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11012528870646839416433591 16518793305970259124650387)
      ·
        refine ⟨24778189958955388686975581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16518793305970259124650387 24778189958955388686975581)
        ·
          refine ⟨9291821234608270757615843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24778189958955388686975581 9291821234608270757615843)
          ·
            refine ⟨13937731851912406136423765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9291821234608270757615843 13937731851912406136423765)
            ·
              refine ⟨10208299696224906838201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 13937731851912406136423765 10208299696224906838201)
              ·
                rfl

theorem cell20_201291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 12].length) (baseStart_201291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201291 prefixEnd_201291 := by exact prefixLift 201291
  have htrace : WordTrace (prefixWord ++ tailWord_201291) baseStart_201291 baseEnd_201291 := by
    simpa [prefixWord, tailWord_201291, baseEnd_201291] using wordTrace_append hprefix tailTrace_201291
  have hstable : (prefixWord ++ tailWord_201291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201291).length < 2 ^ (prefixWord ++ tailWord_201291).sum := by decide
  have hdescent : baseEnd_201291 < baseStart_201291 := by decide
  rcases family_descends (prefixWord ++ tailWord_201291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201297 : List Nat := [1, 2, 2, 1, 3, 4, 3, 2, 2]
def baseStart_201297 : Nat := 118140960795 + 201297 * 2 ^ 59
def prefixEnd_201297 : Nat := 4983230072969 + 3 ^ 40 * 201297 * 2
def baseEnd_201297 : Nat := 91877435829514807343785

theorem tailTrace_201297 : CollatzResearch.WordTrace tailWord_201297 prefixEnd_201297 91877435829514807343785 := by
  unfold tailWord_201297
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341904751742822635674145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4894603167828548423782763 7341904751742822635674145)
  ·
    refine ⟨5506428563807116976755609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7341904751742822635674145 5506428563807116976755609)
    ·
      refine ⟨4129821422855337732566707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5506428563807116976755609 4129821422855337732566707)
      ·
        refine ⟨6194732134283006598850061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129821422855337732566707 6194732134283006598850061)
        ·
          refine ⟨2323024550356127474568773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6194732134283006598850061 2323024550356127474568773)
          ·
            refine ⟨435567103191773901481645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2323024550356127474568773 435567103191773901481645)
            ·
              refine ⟨163337663696915213055617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435567103191773901481645 163337663696915213055617)
              ·
                refine ⟨122503247772686409791713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163337663696915213055617 122503247772686409791713)
                ·
                  refine ⟨91877435829514807343785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122503247772686409791713 91877435829514807343785)
                  ·
                    rfl

theorem cell20_201297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_201297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201297 prefixEnd_201297 := by exact prefixLift 201297
  have htrace : WordTrace (prefixWord ++ tailWord_201297) baseStart_201297 baseEnd_201297 := by
    simpa [prefixWord, tailWord_201297, baseEnd_201297] using wordTrace_append hprefix tailTrace_201297
  have hstable : (prefixWord ++ tailWord_201297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201297).length < 2 ^ (prefixWord ++ tailWord_201297).sum := by decide
  have hdescent : baseEnd_201297 < baseStart_201297 := by decide
  rcases family_descends (prefixWord ++ tailWord_201297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201301 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 4]
def baseStart_201301 : Nat := 118140960795 + 201301 * 2 ^ 59
def prefixEnd_201301 : Nat := 4983230072969 + 3 ^ 40 * 201301 * 2
def baseEnd_201301 : Nat := 91879261538508571210435

theorem tailTrace_201301 : CollatzResearch.WordTrace tailWord_201301 prefixEnd_201301 91879261538508571210435 := by
  unfold tailWord_201301
  simp only [CollatzResearch.WordTrace]
  refine ⟨7342050643728331318819757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4894700429152220879213171 7342050643728331318819757)
  ·
    refine ⟨2753268991398124244557409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7342050643728331318819757 2753268991398124244557409)
    ·
      refine ⟨2064951743548593183418057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2753268991398124244557409 2064951743548593183418057)
      ·
        refine ⟨1548713807661444887563543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2064951743548593183418057 1548713807661444887563543)
        ·
          refine ⟨2323070711492167331345315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548713807661444887563543 2323070711492167331345315)
          ·
            refine ⟨3484606067238250997017973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323070711492167331345315 3484606067238250997017973)
            ·
              refine ⟨326681818803586030970435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3484606067238250997017973 326681818803586030970435)
              ·
                refine ⟨490022728205379046455653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326681818803586030970435 490022728205379046455653)
                ·
                  refine ⟨91879261538508571210435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 490022728205379046455653 91879261538508571210435)
                  ·
                    rfl

theorem cell20_201301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_201301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201301 prefixEnd_201301 := by exact prefixLift 201301
  have htrace : WordTrace (prefixWord ++ tailWord_201301) baseStart_201301 baseEnd_201301 := by
    simpa [prefixWord, tailWord_201301, baseEnd_201301] using wordTrace_append hprefix tailTrace_201301
  have hstable : (prefixWord ++ tailWord_201301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201301).length < 2 ^ (prefixWord ++ tailWord_201301).sum := by decide
  have hdescent : baseEnd_201301 < baseStart_201301 := by decide
  rcases family_descends (prefixWord ++ tailWord_201301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201390 : List Nat := [4, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_201390 : Nat := 118140960795 + 201390 * 2 ^ 59
def prefixEnd_201390 : Nat := 4983230072969 + 3 ^ 40 * 201390 * 2
def baseEnd_201390 : Nat := 91919883563619817243405

theorem tailTrace_201390 : CollatzResearch.WordTrace tailWord_201390 prefixEnd_201390 91919883563619817243405 := by
  unfold tailWord_201390
  simp only [CollatzResearch.WordTrace]
  refine ⟨918162092550737439851203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4896864493603933012539749 918162092550737439851203)
  ·
    refine ⟨1377243138826106159776805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918162092550737439851203 1377243138826106159776805)
    ·
      refine ⟨258233088529894904958151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1377243138826106159776805 258233088529894904958151)
      ·
        refine ⟨387349632794842357437227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258233088529894904958151 387349632794842357437227)
        ·
          refine ⟨581024449192263536155841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387349632794842357437227 581024449192263536155841)
          ·
            refine ⟨435768336894197652116881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581024449192263536155841 435768336894197652116881)
            ·
              refine ⟨326826252670648239087661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435768336894197652116881 326826252670648239087661)
              ·
                refine ⟨122559844751493089657873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326826252670648239087661 122559844751493089657873)
                ·
                  refine ⟨91919883563619817243405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122559844751493089657873 91919883563619817243405)
                  ·
                    rfl

theorem cell20_201390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_201390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201390 prefixEnd_201390 := by exact prefixLift 201390
  have htrace : WordTrace (prefixWord ++ tailWord_201390) baseStart_201390 baseEnd_201390 := by
    simpa [prefixWord, tailWord_201390, baseEnd_201390] using wordTrace_append hprefix tailTrace_201390
  have hstable : (prefixWord ++ tailWord_201390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201390).length < 2 ^ (prefixWord ++ tailWord_201390).sum := by decide
  have hdescent : baseEnd_201390 < baseStart_201390 := by decide
  rcases family_descends (prefixWord ++ tailWord_201390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201408 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 3]
def baseStart_201408 : Nat := 118140960795 + 201408 * 2 ^ 59
def prefixEnd_201408 : Nat := 4983230072969 + 3 ^ 40 * 201408 * 2
def baseEnd_201408 : Nat := 91928099254091754643331

theorem tailTrace_201408 : CollatzResearch.WordTrace tailWord_201408 prefixEnd_201408 91928099254091754643331 := by
  unfold tailWord_201408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3672976627170344296482439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4897302169560459061976585 3672976627170344296482439)
  ·
    refine ⟨5509464940755516444723659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3672976627170344296482439 5509464940755516444723659)
    ·
      refine ⟨8264197411133274667085489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5509464940755516444723659 8264197411133274667085489)
      ·
        refine ⟨6198148058349956000314117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8264197411133274667085489 6198148058349956000314117)
        ·
          refine ⟨1162152760940616750058897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6198148058349956000314117 1162152760940616750058897)
          ·
            refine ⟨871614570705462562544173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162152760940616750058897 871614570705462562544173)
            ·
              refine ⟨326855464014548460954065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 871614570705462562544173 326855464014548460954065)
              ·
                refine ⟨245141598010911345715549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326855464014548460954065 245141598010911345715549)
                ·
                  refine ⟨91928099254091754643331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245141598010911345715549 91928099254091754643331)
                  ·
                    rfl

theorem cell20_201408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_201408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201408 prefixEnd_201408 := by exact prefixLift 201408
  have htrace : WordTrace (prefixWord ++ tailWord_201408) baseStart_201408 baseEnd_201408 := by
    simpa [prefixWord, tailWord_201408, baseEnd_201408] using wordTrace_append hprefix tailTrace_201408
  have hstable : (prefixWord ++ tailWord_201408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201408).length < 2 ^ (prefixWord ++ tailWord_201408).sum := by decide
  have hdescent : baseEnd_201408 < baseStart_201408 := by decide
  rcases family_descends (prefixWord ++ tailWord_201408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201421 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 3]
def baseStart_201421 : Nat := 118140960795 + 201421 * 2 ^ 59
def prefixEnd_201421 : Nat := 4983230072969 + 3 ^ 40 * 201421 * 2
def baseEnd_201421 : Nat := 91934032808321487209945

theorem tailTrace_201421 : CollatzResearch.WordTrace tailWord_201421 prefixEnd_201421 91934032808321487209945 := by
  unfold tailWord_201421
  simp only [CollatzResearch.WordTrace]
  refine ⟨7346427403293591813188117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4897618268862394542125411 7346427403293591813188117)
  ·
    refine ⟨344363784529387116243193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7346427403293591813188117 344363784529387116243193)
    ·
      refine ⟨258272838397040337182395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344363784529387116243193 258272838397040337182395)
      ·
        refine ⟨387409257595560505773593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258272838397040337182395 387409257595560505773593)
        ·
          refine ⟨290556943196670379330195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387409257595560505773593 290556943196670379330195)
          ·
            refine ⟨435835414795005568995293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290556943196670379330195 435835414795005568995293)
            ·
              refine ⟨163438280548127088373235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435835414795005568995293 163438280548127088373235)
              ·
                refine ⟨245157420822190632559853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163438280548127088373235 245157420822190632559853)
                ·
                  refine ⟨91934032808321487209945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245157420822190632559853 91934032808321487209945)
                  ·
                    rfl

theorem cell20_201421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_201421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201421 prefixEnd_201421 := by exact prefixLift 201421
  have htrace : WordTrace (prefixWord ++ tailWord_201421) baseStart_201421 baseEnd_201421 := by
    simpa [prefixWord, tailWord_201421, baseEnd_201421] using wordTrace_append hprefix tailTrace_201421
  have hstable : (prefixWord ++ tailWord_201421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201421).length < 2 ^ (prefixWord ++ tailWord_201421).sum := by decide
  have hdescent : baseEnd_201421 < baseStart_201421 := by decide
  rcases family_descends (prefixWord ++ tailWord_201421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201439 : List Nat := [1, 1, 2, 3, 2, 5, 2, 4]
def baseStart_201439 : Nat := 118140960795 + 201439 * 2 ^ 59
def prefixEnd_201439 : Nat := 4983230072969 + 3 ^ 40 * 201439 * 2
def baseEnd_201439 : Nat := 30647416166264474869957

theorem tailTrace_201439 : CollatzResearch.WordTrace tailWord_201439 prefixEnd_201439 30647416166264474869957 := by
  unfold tailWord_201439
  simp only [CollatzResearch.WordTrace]
  refine ⟨7347083917228380887343371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4898055944818920591562247 7347083917228380887343371)
  ·
    refine ⟨11020625875842571331015057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7347083917228380887343371 11020625875842571331015057)
    ·
      refine ⟨8265469406881928498261293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11020625875842571331015057 8265469406881928498261293)
      ·
        refine ⟨3099551027580723186847985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8265469406881928498261293 3099551027580723186847985)
        ·
          refine ⟨2324663270685542390135989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3099551027580723186847985 2324663270685542390135989)
          ·
            refine ⟨217937181626769599075249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2324663270685542390135989 217937181626769599075249)
            ·
              refine ⟨163452886220077199306437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217937181626769599075249 163452886220077199306437)
              ·
                refine ⟨30647416166264474869957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163452886220077199306437 30647416166264474869957)
                ·
                  rfl

theorem cell20_201439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 4].length) (baseStart_201439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201439 prefixEnd_201439 := by exact prefixLift 201439
  have htrace : WordTrace (prefixWord ++ tailWord_201439) baseStart_201439 baseEnd_201439 := by
    simpa [prefixWord, tailWord_201439, baseEnd_201439] using wordTrace_append hprefix tailTrace_201439
  have hstable : (prefixWord ++ tailWord_201439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201439).length < 2 ^ (prefixWord ++ tailWord_201439).sum := by decide
  have hdescent : baseEnd_201439 < baseStart_201439 := by decide
  rcases family_descends (prefixWord ++ tailWord_201439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201470 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_201470 : Nat := 118140960795 + 201470 * 2 ^ 59
def prefixEnd_201470 : Nat := 4983230072969 + 3 ^ 40 * 201470 * 2
def baseEnd_201470 : Nat := 91956397743495094576411

theorem tailTrace_201470 : CollatzResearch.WordTrace tailWord_201470 prefixEnd_201470 91956397743495094576411 := by
  unfold tailWord_201470
  simp only [CollatzResearch.WordTrace]
  refine ⟨918526822514509147715233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4898809720077382121147909 918526822514509147715233)
  ·
    refine ⟨688895116885881860786425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 918526822514509147715233 688895116885881860786425)
    ·
      refine ⟨516671337664411395589819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 688895116885881860786425 516671337664411395589819)
      ·
        refine ⟨775007006496617093384729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516671337664411395589819 775007006496617093384729)
        ·
          refine ⟨581255254872462820038547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775007006496617093384729 581255254872462820038547)
          ·
            refine ⟨871882882308694230057821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581255254872462820038547 871882882308694230057821)
            ·
              refine ⟨326956080865760336271683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 871882882308694230057821 326956080865760336271683)
              ·
                refine ⟨490434121298640504407525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326956080865760336271683 490434121298640504407525)
                ·
                  refine ⟨91956397743495094576411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 490434121298640504407525 91956397743495094576411)
                  ·
                    rfl

theorem cell20_201470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_201470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201470 prefixEnd_201470 := by exact prefixLift 201470
  have htrace : WordTrace (prefixWord ++ tailWord_201470) baseStart_201470 baseEnd_201470 := by
    simpa [prefixWord, tailWord_201470, baseEnd_201470] using wordTrace_append hprefix tailTrace_201470
  have hstable : (prefixWord ++ tailWord_201470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201470).length < 2 ^ (prefixWord ++ tailWord_201470).sum := by decide
  have hdescent : baseEnd_201470 < baseStart_201470 := by decide
  rcases family_descends (prefixWord ++ tailWord_201470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201481 : List Nat := [1, 2, 1, 1, 3, 2, 3, 7]
def baseStart_201481 : Nat := 118140960795 + 201481 * 2 ^ 59
def prefixEnd_201481 : Nat := 4983230072969 + 3 ^ 40 * 201481 * 2
def baseEnd_201481 : Nat := 30653806147742648403233

theorem tailTrace_201481 : CollatzResearch.WordTrace tailWord_201481 prefixEnd_201481 30653806147742648403233 := by
  unfold tailWord_201481
  simp only [CollatzResearch.WordTrace]
  refine ⟨7348615783076222060372297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4899077188717481373581531 7348615783076222060372297)
  ·
    refine ⟨5511461837307166545279223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7348615783076222060372297 5511461837307166545279223)
    ·
      refine ⟨8267192755960749817918835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5511461837307166545279223 8267192755960749817918835)
      ·
        refine ⟨12400789133941124726878253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8267192755960749817918835 12400789133941124726878253)
        ·
          refine ⟨4650295925227921772579345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12400789133941124726878253 4650295925227921772579345)
          ·
            refine ⟨3487721943920941329434509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4650295925227921772579345 3487721943920941329434509)
            ·
              refine ⟨1307895728970352998537941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3487721943920941329434509 1307895728970352998537941)
              ·
                refine ⟨30653806147742648403233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1307895728970352998537941 30653806147742648403233)
                ·
                  rfl

theorem cell20_201481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_201481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201481 prefixEnd_201481 := by exact prefixLift 201481
  have htrace : WordTrace (prefixWord ++ tailWord_201481) baseStart_201481 baseEnd_201481 := by
    simpa [prefixWord, tailWord_201481, baseEnd_201481] using wordTrace_append hprefix tailTrace_201481
  have hstable : (prefixWord ++ tailWord_201481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201481).length < 2 ^ (prefixWord ++ tailWord_201481).sum := by decide
  have hdescent : baseEnd_201481 < baseStart_201481 := by decide
  rcases family_descends (prefixWord ++ tailWord_201481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201522 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_201522 : Nat := 118140960795 + 201522 * 2 ^ 59
def prefixEnd_201522 : Nat := 4983230072969 + 3 ^ 40 * 201522 * 2
def baseEnd_201522 : Nat := 91980131960414024842865

theorem tailTrace_201522 : CollatzResearch.WordTrace tailWord_201522 prefixEnd_201522 91980131960414024842865 := by
  unfold tailWord_201522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1837527793981921515653705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4900074117285124041743213 1837527793981921515653705)
  ·
    refine ⟨1378145845486441136740279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1837527793981921515653705 1378145845486441136740279)
    ·
      refine ⟨2067218768229661705110419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1378145845486441136740279 2067218768229661705110419)
      ·
        refine ⟨3100828152344492557665629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067218768229661705110419 3100828152344492557665629)
        ·
          refine ⟨1162810557129184709124611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3100828152344492557665629 1162810557129184709124611)
          ·
            refine ⟨1744215835693777063686917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162810557129184709124611 1744215835693777063686917)
            ·
              refine ⟨327040469192583199441297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1744215835693777063686917 327040469192583199441297)
              ·
                refine ⟨245280351894437399580973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327040469192583199441297 245280351894437399580973)
                ·
                  refine ⟨91980131960414024842865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245280351894437399580973 91980131960414024842865)
                  ·
                    rfl

theorem cell20_201522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_201522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201522 prefixEnd_201522 := by exact prefixLift 201522
  have htrace : WordTrace (prefixWord ++ tailWord_201522) baseStart_201522 baseEnd_201522 := by
    simpa [prefixWord, tailWord_201522, baseEnd_201522] using wordTrace_append hprefix tailTrace_201522
  have hstable : (prefixWord ++ tailWord_201522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201522).length < 2 ^ (prefixWord ++ tailWord_201522).sum := by decide
  have hdescent : baseEnd_201522 < baseStart_201522 := by decide
  rcases family_descends (prefixWord ++ tailWord_201522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201525 : List Nat := [1, 3, 3, 1, 3, 1, 4, 2, 2]
def baseStart_201525 : Nat := 118140960795 + 201525 * 2 ^ 59
def prefixEnd_201525 : Nat := 4983230072969 + 3 ^ 40 * 201525 * 2
def baseEnd_201525 : Nat := 91981501242159347742853

theorem tailTrace_201525 : CollatzResearch.WordTrace tailWord_201525 prefixEnd_201525 91981501242159347742853 := by
  unfold tailWord_201525
  simp only [CollatzResearch.WordTrace]
  refine ⟨7350220594916817574974029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4900147063277878383316019 7350220594916817574974029)
  ·
    refine ⟨2756332723093806590615261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7350220594916817574974029 2756332723093806590615261)
    ·
      refine ⟨1033624771160177471480723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2756332723093806590615261 1033624771160177471480723)
      ·
        refine ⟨1550437156740266207221085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033624771160177471480723 1550437156740266207221085)
        ·
          refine ⟨581413933777599827707907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1550437156740266207221085 581413933777599827707907)
          ·
            refine ⟨872120900666399741561861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581413933777599827707907 872120900666399741561861)
            ·
              refine ⟨163522668874949951542849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 872120900666399741561861 163522668874949951542849)
              ·
                refine ⟨122642001656212463657137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163522668874949951542849 122642001656212463657137)
                ·
                  refine ⟨91981501242159347742853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122642001656212463657137 91981501242159347742853)
                  ·
                    rfl

theorem cell20_201525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_201525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201525 prefixEnd_201525 := by exact prefixLift 201525
  have htrace : WordTrace (prefixWord ++ tailWord_201525) baseStart_201525 baseEnd_201525 := by
    simpa [prefixWord, tailWord_201525, baseEnd_201525] using wordTrace_append hprefix tailTrace_201525
  have hstable : (prefixWord ++ tailWord_201525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201525).length < 2 ^ (prefixWord ++ tailWord_201525).sum := by decide
  have hdescent : baseEnd_201525 < baseStart_201525 := by decide
  rcases family_descends (prefixWord ++ tailWord_201525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201553 : List Nat := [1, 2, 2, 1, 6, 1, 3, 4]
def baseStart_201553 : Nat := 118140960795 + 201553 * 2 ^ 59
def prefixEnd_201553 : Nat := 4983230072969 + 3 ^ 40 * 201553 * 2
def baseEnd_201553 : Nat := 30664760401705231603135

theorem tailTrace_201553 : CollatzResearch.WordTrace tailWord_201553 prefixEnd_201553 30664760401705231603135 := by
  unfold tailWord_201553
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351241838815378356993313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4900827892543585571328875 7351241838815378356993313)
  ·
    refine ⟨5513431379111533767744985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7351241838815378356993313 5513431379111533767744985)
    ·
      refine ⟨4135073534333650325808739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5513431379111533767744985 4135073534333650325808739)
      ·
        refine ⟨6202610301500475488713109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135073534333650325808739 6202610301500475488713109)
        ·
          refine ⟨290747357882834788533427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6202610301500475488713109 290747357882834788533427)
          ·
            refine ⟨436121036824252182800141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290747357882834788533427 436121036824252182800141)
            ·
              refine ⟨163545388809094568550053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436121036824252182800141 163545388809094568550053)
              ·
                refine ⟨30664760401705231603135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163545388809094568550053 30664760401705231603135)
                ·
                  rfl

theorem cell20_201553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 4].length) (baseStart_201553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201553 prefixEnd_201553 := by exact prefixLift 201553
  have htrace : WordTrace (prefixWord ++ tailWord_201553) baseStart_201553 baseEnd_201553 := by
    simpa [prefixWord, tailWord_201553, baseEnd_201553] using wordTrace_append hprefix tailTrace_201553
  have hstable : (prefixWord ++ tailWord_201553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201553).length < 2 ^ (prefixWord ++ tailWord_201553).sum := by decide
  have hdescent : baseEnd_201553 < baseStart_201553 := by decide
  rcases family_descends (prefixWord ++ tailWord_201553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201612 : List Nat := [2, 2, 1, 2, 1, 2, 6, 4]
def baseStart_201612 : Nat := 118140960795 + 201612 * 2 ^ 59
def prefixEnd_201612 : Nat := 4983230072969 + 3 ^ 40 * 201612 * 2
def baseEnd_201612 : Nat := 30673736804257903947499

theorem tailTrace_201612 : CollatzResearch.WordTrace tailWord_201612 prefixEnd_201612 30673736804257903947499 := by
  unfold tailWord_201612
  simp only [CollatzResearch.WordTrace]
  refine ⟨3676696872800815716695545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4902262497067754288927393 3676696872800815716695545)
  ·
    refine ⟨2757522654600611787521659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3676696872800815716695545 2757522654600611787521659)
    ·
      refine ⟨4136283981900917681282489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757522654600611787521659 4136283981900917681282489)
      ·
        refine ⟨3102212986425688260961867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4136283981900917681282489 3102212986425688260961867)
        ·
          refine ⟨4653319479638532391442801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102212986425688260961867 4653319479638532391442801)
          ·
            refine ⟨3489989609728899293582101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4653319479638532391442801 3489989609728899293582101)
            ·
              refine ⟨163593262956042154386661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3489989609728899293582101 163593262956042154386661)
              ·
                refine ⟨30673736804257903947499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163593262956042154386661 30673736804257903947499)
                ·
                  rfl

theorem cell20_201612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_201612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201612 prefixEnd_201612 := by exact prefixLift 201612
  have htrace : WordTrace (prefixWord ++ tailWord_201612) baseStart_201612 baseEnd_201612 := by
    simpa [prefixWord, tailWord_201612, baseEnd_201612] using wordTrace_append hprefix tailTrace_201612
  have hstable : (prefixWord ++ tailWord_201612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201612).length < 2 ^ (prefixWord ++ tailWord_201612).sum := by decide
  have hdescent : baseEnd_201612 < baseStart_201612 := by decide
  rcases family_descends (prefixWord ++ tailWord_201612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201618 : List Nat := [3, 2, 3, 2, 2, 2, 1, 3, 2]
def baseStart_201618 : Nat := 118140960795 + 201618 * 2 ^ 59
def prefixEnd_201618 : Nat := 4983230072969 + 3 ^ 40 * 201618 * 2
def baseEnd_201618 : Nat := 92023948976264357642473

theorem tailTrace_201618 : CollatzResearch.WordTrace tailWord_201618 prefixEnd_201618 92023948976264357642473 := by
  unfold tailWord_201618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838403145894973614527377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4902408389053262972073005 1838403145894973614527377)
  ·
    refine ⟨1378802359421230210895533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1838403145894973614527377 1378802359421230210895533)
    ·
      refine ⟨517050884782961329085825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1378802359421230210895533 517050884782961329085825)
      ·
        refine ⟨387788163587220996814369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517050884782961329085825 387788163587220996814369)
        ·
          refine ⟨290841122690415747610777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387788163587220996814369 290841122690415747610777)
          ·
            refine ⟨218130842017811810708083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290841122690415747610777 218130842017811810708083)
            ·
              refine ⟨327196263026717716062125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218130842017811810708083 327196263026717716062125)
              ·
                refine ⟨122698598635019143523297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327196263026717716062125 122698598635019143523297)
                ·
                  refine ⟨92023948976264357642473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122698598635019143523297 92023948976264357642473)
                  ·
                    rfl

theorem cell20_201618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_201618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201618 prefixEnd_201618 := by exact prefixLift 201618
  have htrace : WordTrace (prefixWord ++ tailWord_201618) baseStart_201618 baseEnd_201618 := by
    simpa [prefixWord, tailWord_201618, baseEnd_201618] using wordTrace_append hprefix tailTrace_201618
  have hstable : (prefixWord ++ tailWord_201618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201618).length < 2 ^ (prefixWord ++ tailWord_201618).sum := by decide
  have hdescent : baseEnd_201618 < baseStart_201618 := by decide
  rcases family_descends (prefixWord ++ tailWord_201618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201639 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 4]
def baseStart_201639 : Nat := 118140960795 + 201639 * 2 ^ 59
def prefixEnd_201639 : Nat := 4983230072969 + 3 ^ 40 * 201639 * 2
def baseEnd_201639 : Nat := 92033533948481617942387

theorem tailTrace_201639 : CollatzResearch.WordTrace tailWord_201639 prefixEnd_201639 92033533948481617942387 := by
  unfold tailWord_201639
  simp only [CollatzResearch.WordTrace]
  refine ⟨7354378516503815044623971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4902919011002543363082647 7354378516503815044623971)
  ·
    refine ⟨11031567774755722566935957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7354378516503815044623971 11031567774755722566935957)
    ·
      refine ⟨517104739441674495325123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11031567774755722566935957 517104739441674495325123)
      ·
        refine ⟨775657109162511742987685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517104739441674495325123 775657109162511742987685)
        ·
          refine ⟨145435707967970951810191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 775657109162511742987685 145435707967970951810191)
          ·
            refine ⟨218153561951956427715287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145435707967970951810191 218153561951956427715287)
            ·
              refine ⟨327230342927934641572931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218153561951956427715287 327230342927934641572931)
              ·
                refine ⟨490845514391901962359397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327230342927934641572931 490845514391901962359397)
                ·
                  refine ⟨92033533948481617942387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 490845514391901962359397 92033533948481617942387)
                  ·
                    rfl

theorem cell20_201639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 4].length) (baseStart_201639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201639 prefixEnd_201639 := by exact prefixLift 201639
  have htrace : WordTrace (prefixWord ++ tailWord_201639) baseStart_201639 baseEnd_201639 := by
    simpa [prefixWord, tailWord_201639, baseEnd_201639] using wordTrace_append hprefix tailTrace_201639
  have hstable : (prefixWord ++ tailWord_201639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201639).length < 2 ^ (prefixWord ++ tailWord_201639).sum := by decide
  have hdescent : baseEnd_201639 < baseStart_201639 := by decide
  rcases family_descends (prefixWord ++ tailWord_201639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201671 : List Nat := [1, 1, 4, 1, 1, 2, 4, 6]
def baseStart_201671 : Nat := 118140960795 + 201671 * 2 ^ 59
def prefixEnd_201671 : Nat := 4983230072969 + 3 ^ 40 * 201671 * 2
def baseEnd_201671 : Nat := 30682713206810576291863

theorem tailTrace_201671 : CollatzResearch.WordTrace tailWord_201671 prefixEnd_201671 30682713206810576291863 := by
  unfold tailWord_201671
  simp only [CollatzResearch.WordTrace]
  refine ⟨7355545652387884509788867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4903697101591923006525911 7355545652387884509788867)
  ·
    refine ⟨11033318478581826764683301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7355545652387884509788867 11033318478581826764683301)
    ·
      refine ⟨2068747214734092518378119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11033318478581826764683301 2068747214734092518378119)
      ·
        refine ⟨3103120822101138777567179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068747214734092518378119 3103120822101138777567179)
        ·
          refine ⟨4654681233151708166350769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103120822101138777567179 4654681233151708166350769)
          ·
            refine ⟨3491010924863781124763077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4654681233151708166350769 3491010924863781124763077)
            ·
              refine ⟨654564548411958960893077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3491010924863781124763077 654564548411958960893077)
              ·
                refine ⟨30682713206810576291863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 654564548411958960893077 30682713206810576291863)
                ·
                  rfl

theorem cell20_201671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_201671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201671 prefixEnd_201671 := by exact prefixLift 201671
  have htrace : WordTrace (prefixWord ++ tailWord_201671) baseStart_201671 baseEnd_201671 := by
    simpa [prefixWord, tailWord_201671, baseEnd_201671] using wordTrace_append hprefix tailTrace_201671
  have hstable : (prefixWord ++ tailWord_201671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201671).length < 2 ^ (prefixWord ++ tailWord_201671).sum := by decide
  have hdescent : baseEnd_201671 < baseStart_201671 := by decide
  rcases family_descends (prefixWord ++ tailWord_201671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201681 : List Nat := [1, 2, 2, 1, 2, 1, 4, 5, 2]
def baseStart_201681 : Nat := 118140960795 + 201681 * 2 ^ 59
def prefixEnd_201681 : Nat := 4983230072969 + 3 ^ 40 * 201681 * 2
def baseEnd_201681 : Nat := 92052703892916138542215

theorem tailTrace_201681 : CollatzResearch.WordTrace tailWord_201681 prefixEnd_201681 92052703892916138542215 := by
  unfold tailWord_201681
  simp only [CollatzResearch.WordTrace]
  refine ⟨7355910382351656217652897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4903940254901104145101931 7355910382351656217652897)
  ·
    refine ⟨5516932786763742163239673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7355910382351656217652897 5516932786763742163239673)
    ·
      refine ⟨4137699590072806622429755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5516932786763742163239673 4137699590072806622429755)
      ·
        refine ⟨6206549385109209933644633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4137699590072806622429755 6206549385109209933644633)
        ·
          refine ⟨4654912038831907450233475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6206549385109209933644633 4654912038831907450233475)
          ·
            refine ⟨6982368058247861175350213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4654912038831907450233475 6982368058247861175350213)
            ·
              refine ⟨1309194010921473970378165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6982368058247861175350213 1309194010921473970378165)
              ·
                refine ⟨122736938523888184722953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1309194010921473970378165 122736938523888184722953)
                ·
                  refine ⟨92052703892916138542215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122736938523888184722953 92052703892916138542215)
                  ·
                    rfl

theorem cell20_201681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_201681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201681 prefixEnd_201681 := by exact prefixLift 201681
  have htrace : WordTrace (prefixWord ++ tailWord_201681) baseStart_201681 baseEnd_201681 := by
    simpa [prefixWord, tailWord_201681, baseEnd_201681] using wordTrace_append hprefix tailTrace_201681
  have hstable : (prefixWord ++ tailWord_201681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201681).length < 2 ^ (prefixWord ++ tailWord_201681).sum := by decide
  have hdescent : baseEnd_201681 < baseStart_201681 := by decide
  rcases family_descends (prefixWord ++ tailWord_201681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201736 : List Nat := [2, 1, 3, 2, 1, 4, 2, 3, 2]
def baseStart_201736 : Nat := 118140960795 + 201736 * 2 ^ 59
def prefixEnd_201736 : Nat := 4983230072969 + 3 ^ 40 * 201736 * 2
def baseEnd_201736 : Nat := 92077807391580391708657

theorem tailTrace_201736 : CollatzResearch.WordTrace tailWord_201736 prefixEnd_201736 92077807391580391708657 := by
  unfold tailWord_201736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3678958198576200305452531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4905277598101600407270041 3678958198576200305452531)
  ·
    refine ⟨5518437297864300458178797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3678958198576200305452531 5518437297864300458178797)
    ·
      refine ⟨2069413986699112671817049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5518437297864300458178797 2069413986699112671817049)
      ·
        refine ⟨1552060490024334503862787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2069413986699112671817049 1552060490024334503862787)
        ·
          refine ⟨2328090735036501755794181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552060490024334503862787 2328090735036501755794181)
          ·
            refine ⟨436517012819344079211409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2328090735036501755794181 436517012819344079211409)
            ·
              refine ⟨327387759614508059408557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436517012819344079211409 327387759614508059408557)
              ·
                refine ⟨122770409855440522278209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327387759614508059408557 122770409855440522278209)
                ·
                  refine ⟨92077807391580391708657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122770409855440522278209 92077807391580391708657)
                  ·
                    rfl

theorem cell20_201736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_201736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201736 prefixEnd_201736 := by exact prefixLift 201736
  have htrace : WordTrace (prefixWord ++ tailWord_201736) baseStart_201736 baseEnd_201736 := by
    simpa [prefixWord, tailWord_201736, baseEnd_201736] using wordTrace_append hprefix tailTrace_201736
  have hstable : (prefixWord ++ tailWord_201736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201736).length < 2 ^ (prefixWord ++ tailWord_201736).sum := by decide
  have hdescent : baseEnd_201736 < baseStart_201736 := by decide
  rcases family_descends (prefixWord ++ tailWord_201736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201746 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 5]
def baseStart_201746 : Nat := 118140960795 + 201746 * 2 ^ 59
def prefixEnd_201746 : Nat := 4983230072969 + 3 ^ 40 * 201746 * 2
def baseEnd_201746 : Nat := 92082371664064801375283

theorem tailTrace_201746 : CollatzResearch.WordTrace tailWord_201746 prefixEnd_201746 92082371664064801375283 := by
  unfold tailWord_201746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839570281779043079692273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4905520751410781545846061 1839570281779043079692273)
  ·
    refine ⟨1379677711334282309769205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1839570281779043079692273 1379677711334282309769205)
    ·
      refine ⟨129344785437588966540863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1379677711334282309769205 129344785437588966540863)
      ·
        refine ⟨194017178156383449811295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129344785437588966540863 194017178156383449811295)
        ·
          refine ⟨291025767234575174716943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194017178156383449811295 291025767234575174716943)
          ·
            refine ⟨436538650851862762075415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291025767234575174716943 436538650851862762075415)
            ·
              refine ⟨654807976277794143113123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436538650851862762075415 654807976277794143113123)
              ·
                refine ⟨982211964416691214669685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654807976277794143113123 982211964416691214669685)
                ·
                  refine ⟨92082371664064801375283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 982211964416691214669685 92082371664064801375283)
                  ·
                    rfl

theorem cell20_201746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_201746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201746 prefixEnd_201746 := by exact prefixLift 201746
  have htrace : WordTrace (prefixWord ++ tailWord_201746) baseStart_201746 baseEnd_201746 := by
    simpa [prefixWord, tailWord_201746, baseEnd_201746] using wordTrace_append hprefix tailTrace_201746
  have hstable : (prefixWord ++ tailWord_201746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201746).length < 2 ^ (prefixWord ++ tailWord_201746).sum := by decide
  have hdescent : baseEnd_201746 < baseStart_201746 := by decide
  rcases family_descends (prefixWord ++ tailWord_201746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201778 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_201778 : Nat := 118140960795 + 201778 * 2 ^ 59
def prefixEnd_201778 : Nat := 4983230072969 + 3 ^ 40 * 201778 * 2
def baseEnd_201778 : Nat := 92096977336014912308485

theorem tailTrace_201778 : CollatzResearch.WordTrace tailWord_201778 prefixEnd_201778 92096977336014912308485 := by
  unfold tailWord_201778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839862065750060445983497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4906298842000161189289325 1839862065750060445983497)
  ·
    refine ⟨1379896549312545334487623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1839862065750060445983497 1379896549312545334487623)
    ·
      refine ⟨2069844823968818001731435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379896549312545334487623 2069844823968818001731435)
      ·
        refine ⟨3104767235953227002597153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069844823968818001731435 3104767235953227002597153)
        ·
          refine ⟨2328575426964920251947865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3104767235953227002597153 2328575426964920251947865)
          ·
            refine ⟨1746431570223690188960899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2328575426964920251947865 1746431570223690188960899)
            ·
              refine ⟨2619647355335535283441349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746431570223690188960899 2619647355335535283441349)
              ·
                refine ⟨491183879125412865645253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2619647355335535283441349 491183879125412865645253)
                ·
                  refine ⟨92096977336014912308485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 491183879125412865645253 92096977336014912308485)
                  ·
                    rfl

theorem cell20_201778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_201778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201778 prefixEnd_201778 := by exact prefixLift 201778
  have htrace : WordTrace (prefixWord ++ tailWord_201778) baseStart_201778 baseEnd_201778 := by
    simpa [prefixWord, tailWord_201778, baseEnd_201778] using wordTrace_append hprefix tailTrace_201778
  have hstable : (prefixWord ++ tailWord_201778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201778).length < 2 ^ (prefixWord ++ tailWord_201778).sum := by decide
  have hdescent : baseEnd_201778 < baseStart_201778 := by decide
  rcases family_descends (prefixWord ++ tailWord_201778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201792 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_201792 : Nat := 118140960795 + 201792 * 2 ^ 59
def prefixEnd_201792 : Nat := 4983230072969 + 3 ^ 40 * 201792 * 2
def baseEnd_201792 : Nat := 92103367317493085841761

theorem tailTrace_201792 : CollatzResearch.WordTrace tailWord_201792 prefixEnd_201792 92103367317493085841761 := by
  unfold tailWord_201792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679979442474761087471815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4906639256633014783295753 3679979442474761087471815)
  ·
    refine ⟨5519969163712141631207723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3679979442474761087471815 5519969163712141631207723)
    ·
      refine ⟨8279953745568212446811585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5519969163712141631207723 8279953745568212446811585)
      ·
        refine ⟨6209965309176159335108689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8279953745568212446811585 6209965309176159335108689)
        ·
          refine ⟨4657473981882119501331517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6209965309176159335108689 4657473981882119501331517)
          ·
            refine ⟨1746552743205794812999319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4657473981882119501331517 1746552743205794812999319)
            ·
              refine ⟨2619829114808692219498979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746552743205794812999319 2619829114808692219498979)
              ·
                refine ⟨3929743672213038329248469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619829114808692219498979 3929743672213038329248469)
                ·
                  refine ⟨92103367317493085841761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3929743672213038329248469 92103367317493085841761)
                  ·
                    rfl

theorem cell20_201792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_201792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201792 prefixEnd_201792 := by exact prefixLift 201792
  have htrace : WordTrace (prefixWord ++ tailWord_201792) baseStart_201792 baseEnd_201792 := by
    simpa [prefixWord, tailWord_201792, baseEnd_201792] using wordTrace_append hprefix tailTrace_201792
  have hstable : (prefixWord ++ tailWord_201792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201792).length < 2 ^ (prefixWord ++ tailWord_201792).sum := by decide
  have hdescent : baseEnd_201792 < baseStart_201792 := by decide
  rcases family_descends (prefixWord ++ tailWord_201792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201822 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_201822 : Nat := 118140960795 + 201822 * 2 ^ 59
def prefixEnd_201822 : Nat := 4983230072969 + 3 ^ 40 * 201822 * 2
def baseEnd_201822 : Nat := 92117060134946314841639

theorem tailTrace_201822 : CollatzResearch.WordTrace tailWord_201822 prefixEnd_201822 92117060134946314841639 := by
  unfold tailWord_201822
  simp only [CollatzResearch.WordTrace]
  refine ⟨920131634355104662316965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4907368716560558199023813 920131634355104662316965)
  ·
    refine ⟨172524681441582124184431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 920131634355104662316965 172524681441582124184431)
    ·
      refine ⟨258787022162373186276647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172524681441582124184431 258787022162373186276647)
      ·
        refine ⟨388180533243559779414971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258787022162373186276647 388180533243559779414971)
        ·
          refine ⟨582270799865339669122457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388180533243559779414971 582270799865339669122457)
          ·
            refine ⟨436703099899004751841843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582270799865339669122457 436703099899004751841843)
            ·
              refine ⟨655054649848507127762765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436703099899004751841843 655054649848507127762765)
              ·
                refine ⟨245645493693190172911037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 655054649848507127762765 245645493693190172911037)
                ·
                  refine ⟨92117060134946314841639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245645493693190172911037 92117060134946314841639)
                  ·
                    rfl

theorem cell20_201822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_201822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201822 prefixEnd_201822 := by exact prefixLift 201822
  have htrace : WordTrace (prefixWord ++ tailWord_201822) baseStart_201822 baseEnd_201822 := by
    simpa [prefixWord, tailWord_201822, baseEnd_201822] using wordTrace_append hprefix tailTrace_201822
  have hstable : (prefixWord ++ tailWord_201822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201822).length < 2 ^ (prefixWord ++ tailWord_201822).sum := by decide
  have hdescent : baseEnd_201822 < baseStart_201822 := by decide
  rcases family_descends (prefixWord ++ tailWord_201822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201823 : List Nat := [1, 1, 2, 3, 1, 1, 6, 5]
def baseStart_201823 : Nat := 118140960795 + 201823 * 2 ^ 59
def prefixEnd_201823 : Nat := 4983230072969 + 3 ^ 40 * 201823 * 2
def baseEnd_201823 : Nat := 30705838854064918602767

theorem tailTrace_201823 : CollatzResearch.WordTrace tailWord_201823 prefixEnd_201823 30705838854064918602767 := by
  unfold tailWord_201823
  simp only [CollatzResearch.WordTrace]
  refine ⟨7361089547837214469322123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4907393031891476312881415 7361089547837214469322123)
  ·
    refine ⟨11041634321755821703983185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7361089547837214469322123 11041634321755821703983185)
    ·
      refine ⟨8281225741316866277987389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11041634321755821703983185 8281225741316866277987389)
      ·
        refine ⟨3105459652993824854245271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8281225741316866277987389 3105459652993824854245271)
        ·
          refine ⟨4658189479490737281367907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105459652993824854245271 4658189479490737281367907)
          ·
            refine ⟨6987284219236105922051861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658189479490737281367907 6987284219236105922051861)
            ·
              refine ⟨327528947776692465096181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6987284219236105922051861 327528947776692465096181)
              ·
                refine ⟨30705838854064918602767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327528947776692465096181 30705838854064918602767)
                ·
                  rfl

theorem cell20_201823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_201823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201823 prefixEnd_201823 := by exact prefixLift 201823
  have htrace : WordTrace (prefixWord ++ tailWord_201823) baseStart_201823 baseEnd_201823 := by
    simpa [prefixWord, tailWord_201823, baseEnd_201823] using wordTrace_append hprefix tailTrace_201823
  have hstable : (prefixWord ++ tailWord_201823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201823).length < 2 ^ (prefixWord ++ tailWord_201823).sum := by decide
  have hdescent : baseEnd_201823 < baseStart_201823 := by decide
  rcases family_descends (prefixWord ++ tailWord_201823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201861 : List Nat := [1, 3, 1, 1, 6, 8]
def baseStart_201861 : Nat := 118140960795 + 201861 * 2 ^ 59
def prefixEnd_201861 : Nat := 4983230072969 + 3 ^ 40 * 201861 * 2
def baseEnd_201861 : Nat := 3412402251764278242277

theorem tailTrace_201861 : CollatzResearch.WordTrace tailWord_201861 prefixEnd_201861 3412402251764278242277 := by
  unfold tailWord_201861
  simp only [CollatzResearch.WordTrace]
  refine ⟨7362475521699546959205437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4908317014466364639470291 7362475521699546959205437)
  ·
    refine ⟨2760928320637330109702039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7362475521699546959205437 2760928320637330109702039)
    ·
      refine ⟨4141392480955995164553059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2760928320637330109702039 4141392480955995164553059)
      ·
        refine ⟨6212088721433992746829589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4141392480955995164553059 6212088721433992746829589)
        ·
          refine ⟨291191658817218410007637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6212088721433992746829589 291191658817218410007637)
          ·
            refine ⟨3412402251764278242277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 291191658817218410007637 3412402251764278242277)
            ·
              rfl

theorem cell20_201861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 8].length) (baseStart_201861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201861 prefixEnd_201861 := by exact prefixLift 201861
  have htrace : WordTrace (prefixWord ++ tailWord_201861) baseStart_201861 baseEnd_201861 := by
    simpa [prefixWord, tailWord_201861, baseEnd_201861] using wordTrace_append hprefix tailTrace_201861
  have hstable : (prefixWord ++ tailWord_201861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201861).length < 2 ^ (prefixWord ++ tailWord_201861).sum := by decide
  have hdescent : baseEnd_201861 < baseStart_201861 := by decide
  rcases family_descends (prefixWord ++ tailWord_201861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201868 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_201868 : Nat := 118140960795 + 201868 * 2 ^ 59
def prefixEnd_201868 : Nat := 4983230072969 + 3 ^ 40 * 201868 * 2
def baseEnd_201868 : Nat := 92138055788374599308117

theorem tailTrace_201868 : CollatzResearch.WordTrace tailWord_201868 prefixEnd_201868 92138055788374599308117 := by
  unfold tailWord_201868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681365416337093577355129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4908487221782791436473505 3681365416337093577355129)
  ·
    refine ⟨2761024062252820183016347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3681365416337093577355129 2761024062252820183016347)
    ·
      refine ⟨4141536093379230274524521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2761024062252820183016347 4141536093379230274524521)
      ·
        refine ⟨3106152070034422705893391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4141536093379230274524521 3106152070034422705893391)
        ·
          refine ⟨4659228105051634058840087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106152070034422705893391 4659228105051634058840087)
          ·
            refine ⟨6988842157577451088260131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659228105051634058840087 6988842157577451088260131)
            ·
              refine ⟨10483263236366176632390197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6988842157577451088260131 10483263236366176632390197)
              ·
                refine ⟨982805928409329059286581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10483263236366176632390197 982805928409329059286581)
                ·
                  refine ⟨92138055788374599308117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 982805928409329059286581 92138055788374599308117)
                  ·
                    rfl

theorem cell20_201868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_201868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201868 prefixEnd_201868 := by exact prefixLift 201868
  have htrace : WordTrace (prefixWord ++ tailWord_201868) baseStart_201868 baseEnd_201868 := by
    simpa [prefixWord, tailWord_201868, baseEnd_201868] using wordTrace_append hprefix tailTrace_201868
  have hstable : (prefixWord ++ tailWord_201868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201868).length < 2 ^ (prefixWord ++ tailWord_201868).sum := by decide
  have hdescent : baseEnd_201868 < baseStart_201868 := by decide
  rcases family_descends (prefixWord ++ tailWord_201868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201885 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 3]
def baseStart_201885 : Nat := 118140960795 + 201885 * 2 ^ 59
def prefixEnd_201885 : Nat := 4983230072969 + 3 ^ 40 * 201885 * 2
def baseEnd_201885 : Nat := 92145815051598095741381

theorem tailTrace_201885 : CollatzResearch.WordTrace tailWord_201885 prefixEnd_201885 92145815051598095741381 := by
  unfold tailWord_201885
  simp only [CollatzResearch.WordTrace]
  refine ⟨7363350873612599058079109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4908900582408399372052739 7363350873612599058079109)
  ·
    refine ⟨1380628288802362323389833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7363350873612599058079109 1380628288802362323389833)
    ·
      refine ⟨1035471216601771742542375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1380628288802362323389833 1035471216601771742542375)
      ·
        refine ⟨1553206824902657613813563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035471216601771742542375 1553206824902657613813563)
        ·
          refine ⟨2329810237353986420720345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553206824902657613813563 2329810237353986420720345)
          ·
            refine ⟨1747357678015489815540259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2329810237353986420720345 1747357678015489815540259)
            ·
              refine ⟨2621036517023234723310389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747357678015489815540259 2621036517023234723310389)
              ·
                refine ⟨245722173470928255310349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2621036517023234723310389 245722173470928255310349)
                ·
                  refine ⟨92145815051598095741381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245722173470928255310349 92145815051598095741381)
                  ·
                    rfl

theorem cell20_201885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_201885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201885 prefixEnd_201885 := by exact prefixLift 201885
  have htrace : WordTrace (prefixWord ++ tailWord_201885) baseStart_201885 baseEnd_201885 := by
    simpa [prefixWord, tailWord_201885, baseEnd_201885] using wordTrace_append hprefix tailTrace_201885
  have hstable : (prefixWord ++ tailWord_201885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201885).length < 2 ^ (prefixWord ++ tailWord_201885).sum := by decide
  have hdescent : baseEnd_201885 < baseStart_201885 := by decide
  rcases family_descends (prefixWord ++ tailWord_201885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201892 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_201892 : Nat := 118140960795 + 201892 * 2 ^ 59
def prefixEnd_201892 : Nat := 4983230072969 + 3 ^ 40 * 201892 * 2
def baseEnd_201892 : Nat := 92149010042337182508019

theorem tailTrace_201892 : CollatzResearch.WordTrace tailWord_201892 prefixEnd_201892 92149010042337182508019 := by
  unfold tailWord_201892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681803092293619626791965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4909070789724826169055953 3681803092293619626791965)
  ·
    refine ⟨1380676159610107360046987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3681803092293619626791965 1380676159610107360046987)
    ·
      refine ⟨2071014239415161040070481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1380676159610107360046987 2071014239415161040070481)
      ·
        refine ⟨1553260679561370780052861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2071014239415161040070481 1553260679561370780052861)
        ·
          refine ⟨582472754835514042519823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1553260679561370780052861 582472754835514042519823)
          ·
            refine ⟨873709132253271063779735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582472754835514042519823 873709132253271063779735)
            ·
              refine ⟨1310563698379906595669603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873709132253271063779735 1310563698379906595669603)
              ·
                refine ⟨1965845547569859893504405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310563698379906595669603 1965845547569859893504405)
                ·
                  refine ⟨92149010042337182508019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1965845547569859893504405 92149010042337182508019)
                  ·
                    rfl

theorem cell20_201892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_201892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201892 prefixEnd_201892 := by exact prefixLift 201892
  have htrace : WordTrace (prefixWord ++ tailWord_201892) baseStart_201892 baseEnd_201892 := by
    simpa [prefixWord, tailWord_201892, baseEnd_201892] using wordTrace_append hprefix tailTrace_201892
  have hstable : (prefixWord ++ tailWord_201892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201892).length < 2 ^ (prefixWord ++ tailWord_201892).sum := by decide
  have hdescent : baseEnd_201892 < baseStart_201892 := by decide
  rcases family_descends (prefixWord ++ tailWord_201892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201895 : List Nat := [1, 1, 6, 2, 1, 2, 3, 4]
def baseStart_201895 : Nat := 118140960795 + 201895 * 2 ^ 59
def prefixEnd_201895 : Nat := 4983230072969 + 3 ^ 40 * 201895 * 2
def baseEnd_201895 : Nat := 30716793108027501802669

theorem tailTrace_201895 : CollatzResearch.WordTrace tailWord_201895 prefixEnd_201895 30716793108027501802669 := by
  unfold tailWord_201895
  simp only [CollatzResearch.WordTrace]
  refine ⟨7363715603576370765943139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4909143735717580510628759 7363715603576370765943139)
  ·
    refine ⟨11045573405364556148914709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7363715603576370765943139 11045573405364556148914709)
    ·
      refine ⟨517761253376463569480377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11045573405364556148914709 517761253376463569480377)
      ·
        refine ⟨388320940032347677110283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517761253376463569480377 388320940032347677110283)
        ·
          refine ⟨582481410048521515665425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388320940032347677110283 582481410048521515665425)
          ·
            refine ⟨436861057536391136749069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582481410048521515665425 436861057536391136749069)
            ·
              refine ⟨163822896576146676280901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436861057536391136749069 163822896576146676280901)
              ·
                refine ⟨30716793108027501802669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163822896576146676280901 30716793108027501802669)
                ·
                  rfl

theorem cell20_201895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 4].length) (baseStart_201895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201895 prefixEnd_201895 := by exact prefixLift 201895
  have htrace : WordTrace (prefixWord ++ tailWord_201895) baseStart_201895 baseEnd_201895 := by
    simpa [prefixWord, tailWord_201895, baseEnd_201895] using wordTrace_append hprefix tailTrace_201895
  have hstable : (prefixWord ++ tailWord_201895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201895).length < 2 ^ (prefixWord ++ tailWord_201895).sum := by decide
  have hdescent : baseEnd_201895 < baseStart_201895 := by decide
  rcases family_descends (prefixWord ++ tailWord_201895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201930 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_201930 : Nat := 118140960795 + 201930 * 2 ^ 59
def prefixEnd_201930 : Nat := 4983230072969 + 3 ^ 40 * 201930 * 2
def baseEnd_201930 : Nat := 92166354277777939241197

theorem tailTrace_201930 : CollatzResearch.WordTrace tailWord_201930 prefixEnd_201930 92166354277777939241197 := by
  unfold tailWord_201930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1841248039612392935866811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4909994772299714495644829 1841248039612392935866811)
  ·
    refine ⟨2761872059418589403800217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1841248039612392935866811 2761872059418589403800217)
    ·
      refine ⟨2071404044563942052850163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2761872059418589403800217 2071404044563942052850163)
      ·
        refine ⟨3107106066845913079275245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2071404044563942052850163 3107106066845913079275245)
        ·
          refine ⟨1165164775067217404728217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3107106066845913079275245 1165164775067217404728217)
          ·
            refine ⟨873873581300413053546163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1165164775067217404728217 873873581300413053546163)
            ·
              refine ⟨1310810371950619580319245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873873581300413053546163 1310810371950619580319245)
              ·
                refine ⟨491553889481482342619717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1310810371950619580319245 491553889481482342619717)
                ·
                  refine ⟨92166354277777939241197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 491553889481482342619717 92166354277777939241197)
                  ·
                    rfl

theorem cell20_201930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_201930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201930 prefixEnd_201930 := by exact prefixLift 201930
  have htrace : WordTrace (prefixWord ++ tailWord_201930) baseStart_201930 baseEnd_201930 := by
    simpa [prefixWord, tailWord_201930, baseEnd_201930] using wordTrace_append hprefix tailTrace_201930
  have hstable : (prefixWord ++ tailWord_201930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201930).length < 2 ^ (prefixWord ++ tailWord_201930).sum := by decide
  have hdescent : baseEnd_201930 < baseStart_201930 := by decide
  rcases family_descends (prefixWord ++ tailWord_201930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201964 : List Nat := [2, 2, 1, 1, 2, 6, 1, 3, 2]
def baseStart_201964 : Nat := 118140960795 + 201964 * 2 ^ 59
def prefixEnd_201964 : Nat := 4983230072969 + 3 ^ 40 * 201964 * 2
def baseEnd_201964 : Nat := 92181872804224932107725

theorem tailTrace_201964 : CollatzResearch.WordTrace tailWord_201964 prefixEnd_201964 92181872804224932107725 := by
  unfold tailWord_201964
  simp only [CollatzResearch.WordTrace]
  refine ⟨3683116120163197775102473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4910821493550930366803297 3683116120163197775102473)
  ·
    refine ⟨2762337090122398331326855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3683116120163197775102473 2762337090122398331326855)
    ·
      refine ⟨4143505635183597496990283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2762337090122398331326855 4143505635183597496990283)
      ·
        refine ⟨6215258452775396245485425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4143505635183597496990283 6215258452775396245485425)
        ·
          refine ⟨4661443839581547184114069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6215258452775396245485425 4661443839581547184114069)
          ·
            refine ⟨218505179980385024255347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4661443839581547184114069 218505179980385024255347)
            ·
              refine ⟨327757769970577536383021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218505179980385024255347 327757769970577536383021)
              ·
                refine ⟨122909163738966576143633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327757769970577536383021 122909163738966576143633)
                ·
                  refine ⟨92181872804224932107725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122909163738966576143633 92181872804224932107725)
                  ·
                    rfl

theorem cell20_201964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_201964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201964 prefixEnd_201964 := by exact prefixLift 201964
  have htrace : WordTrace (prefixWord ++ tailWord_201964) baseStart_201964 baseEnd_201964 := by
    simpa [prefixWord, tailWord_201964, baseEnd_201964] using wordTrace_append hprefix tailTrace_201964
  have hstable : (prefixWord ++ tailWord_201964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201964).length < 2 ^ (prefixWord ++ tailWord_201964).sum := by decide
  have hdescent : baseEnd_201964 < baseStart_201964 := by decide
  rcases family_descends (prefixWord ++ tailWord_201964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201985 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 4]
def baseStart_201985 : Nat := 118140960795 + 201985 * 2 ^ 59
def prefixEnd_201985 : Nat := 4983230072969 + 3 ^ 40 * 201985 * 2
def baseEnd_201985 : Nat := 92191457776442192407639

theorem tailTrace_201985 : CollatzResearch.WordTrace tailWord_201985 prefixEnd_201985 92191457776442192407639 := by
  unfold tailWord_201985
  simp only [CollatzResearch.WordTrace]
  refine ⟨7366998173250316136719409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4911332115500210757812939 7366998173250316136719409)
  ·
    refine ⟨5525248629937737102539557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7366998173250316136719409 5525248629937737102539557)
    ·
      refine ⟨1035984118113325706726167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5525248629937737102539557 1035984118113325706726167)
      ·
        refine ⟨1553976177169988560089251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035984118113325706726167 1553976177169988560089251)
        ·
          refine ⟨2330964265754982840133877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553976177169988560089251 2330964265754982840133877)
          ·
            refine ⟨218527899914529641262551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2330964265754982840133877 218527899914529641262551)
            ·
              refine ⟨327791849871794461893827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218527899914529641262551 327791849871794461893827)
              ·
                refine ⟨491687774807691692840741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327791849871794461893827 491687774807691692840741)
                ·
                  refine ⟨92191457776442192407639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 491687774807691692840741 92191457776442192407639)
                  ·
                    rfl

theorem cell20_201985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_201985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201985 prefixEnd_201985 := by exact prefixLift 201985
  have htrace : WordTrace (prefixWord ++ tailWord_201985) baseStart_201985 baseEnd_201985 := by
    simpa [prefixWord, tailWord_201985, baseEnd_201985] using wordTrace_append hprefix tailTrace_201985
  have hstable : (prefixWord ++ tailWord_201985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201985).length < 2 ^ (prefixWord ++ tailWord_201985).sum := by decide
  have hdescent : baseEnd_201985 < baseStart_201985 := by decide
  rcases family_descends (prefixWord ++ tailWord_201985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201992 : List Nat := [2, 1, 3, 2, 4, 1, 2, 5]
def baseStart_201992 : Nat := 118140960795 + 201992 * 2 ^ 59
def prefixEnd_201992 : Nat := 4983230072969 + 3 ^ 40 * 201992 * 2
def baseEnd_201992 : Nat := 30731550922393759724759

theorem tailTrace_201992 : CollatzResearch.WordTrace tailWord_201992 prefixEnd_201992 30731550922393759724759 := by
  unfold tailWord_201992
  simp only [CollatzResearch.WordTrace]
  refine ⟨3683626742112478166112115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4911502322816637554816153 3683626742112478166112115)
  ·
    refine ⟨5525440113168717249168173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3683626742112478166112115 5525440113168717249168173)
    ·
      refine ⟨2072040042438268968438065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5525440113168717249168173 2072040042438268968438065)
      ·
        refine ⟨1554030031828701726328549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2072040042438268968438065 1554030031828701726328549)
        ·
          refine ⟨291380630967881573686603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1554030031828701726328549 291380630967881573686603)
          ·
            refine ⟨437070946451822360529905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291380630967881573686603 437070946451822360529905)
            ·
              refine ⟨327803209838866770397429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437070946451822360529905 327803209838866770397429)
              ·
                refine ⟨30731550922393759724759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327803209838866770397429 30731550922393759724759)
                ·
                  rfl

theorem cell20_201992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_201992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201992 prefixEnd_201992 := by exact prefixLift 201992
  have htrace : WordTrace (prefixWord ++ tailWord_201992) baseStart_201992 baseEnd_201992 := by
    simpa [prefixWord, tailWord_201992, baseEnd_201992] using wordTrace_append hprefix tailTrace_201992
  have hstable : (prefixWord ++ tailWord_201992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201992).length < 2 ^ (prefixWord ++ tailWord_201992).sum := by decide
  have hdescent : baseEnd_201992 < baseStart_201992 := by decide
  rcases family_descends (prefixWord ++ tailWord_201992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202037 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 3]
def baseStart_202037 : Nat := 118140960795 + 202037 * 2 ^ 59
def prefixEnd_202037 : Nat := 4983230072969 + 3 ^ 40 * 202037 * 2
def baseEnd_202037 : Nat := 92215191993361122674093

theorem tailTrace_202037 : CollatzResearch.WordTrace tailWord_202037 prefixEnd_202037 92215191993361122674093 := by
  unfold tailWord_202037
  simp only [CollatzResearch.WordTrace]
  refine ⟨7368894769061929017612365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4912596512707952678408243 7368894769061929017612365)
  ·
    refine ⟨2763335538398223381604637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7368894769061929017612365 2763335538398223381604637)
    ·
      refine ⟨1036250826899333768101739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2763335538398223381604637 1036250826899333768101739)
      ·
        refine ⟨1554376240349000652152609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036250826899333768101739 1554376240349000652152609)
        ·
          refine ⟨1165782180261750489114457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1554376240349000652152609 1165782180261750489114457)
          ·
            refine ⟨874336635196312866835843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1165782180261750489114457 874336635196312866835843)
            ·
              refine ⟨1311504952794469300253765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874336635196312866835843 1311504952794469300253765)
              ·
                refine ⟨245907178648962993797581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1311504952794469300253765 245907178648962993797581)
                ·
                  refine ⟨92215191993361122674093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245907178648962993797581 92215191993361122674093)
                  ·
                    rfl

theorem cell20_202037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_202037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202037 prefixEnd_202037 := by exact prefixLift 202037
  have htrace : WordTrace (prefixWord ++ tailWord_202037) baseStart_202037 baseEnd_202037 := by
    simpa [prefixWord, tailWord_202037, baseEnd_202037] using wordTrace_append hprefix tailTrace_202037
  have hstable : (prefixWord ++ tailWord_202037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202037).length < 2 ^ (prefixWord ++ tailWord_202037).sum := by decide
  have hdescent : baseEnd_202037 < baseStart_202037 := by decide
  rcases family_descends (prefixWord ++ tailWord_202037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202068 : List Nat := [2, 4, 1, 1, 2, 1, 5, 4]
def baseStart_202068 : Nat := 118140960795 + 202068 * 2 ^ 59
def prefixEnd_202068 : Nat := 4983230072969 + 3 ^ 40 * 202068 * 2
def baseEnd_202068 : Nat := 30743113746020930880211

theorem tailTrace_202068 : CollatzResearch.WordTrace tailWord_202068 prefixEnd_202068 30743113746020930880211 := by
  unfold tailWord_202068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685012715974810655995429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4913350287966414207993905 3685012715974810655995429)
  ·
    refine ⟨690939884245276997999143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3685012715974810655995429 690939884245276997999143)
    ·
      refine ⟨1036409826367915496998715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 690939884245276997999143 1036409826367915496998715)
      ·
        refine ⟨1554614739551873245498073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036409826367915496998715 1554614739551873245498073)
        ·
          refine ⟨1165961054663904934123555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1554614739551873245498073 1165961054663904934123555)
          ·
            refine ⟨1748941581995857401185333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165961054663904934123555 1748941581995857401185333)
            ·
              refine ⟨163963273312111631361125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1748941581995857401185333 163963273312111631361125)
              ·
                refine ⟨30743113746020930880211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163963273312111631361125 30743113746020930880211)
                ·
                  rfl

theorem cell20_202068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_202068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202068 prefixEnd_202068 := by exact prefixLift 202068
  have htrace : WordTrace (prefixWord ++ tailWord_202068) baseStart_202068 baseEnd_202068 := by
    simpa [prefixWord, tailWord_202068, baseEnd_202068] using wordTrace_append hprefix tailTrace_202068
  have hstable : (prefixWord ++ tailWord_202068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202068).length < 2 ^ (prefixWord ++ tailWord_202068).sum := by decide
  have hdescent : baseEnd_202068 < baseStart_202068 := by decide
  rcases family_descends (prefixWord ++ tailWord_202068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202082 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_202082 : Nat := 118140960795 + 202082 * 2 ^ 59
def prefixEnd_202082 : Nat := 4983230072969 + 3 ^ 40 * 202082 * 2
def baseEnd_202082 : Nat := 92235731219540966173909

theorem tailTrace_202082 : CollatzResearch.WordTrace tailWord_202082 prefixEnd_202082 92235731219540966173909 := by
  unfold tailWord_202082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842634013474725425750125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4913690702599267802000333 1842634013474725425750125)
  ·
    refine ⟨690987755053022034656297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1842634013474725425750125 690987755053022034656297)
    ·
      refine ⟨518240816289766525992223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 690987755053022034656297 518240816289766525992223)
      ·
        refine ⟨777361224434649788988335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518240816289766525992223 777361224434649788988335)
        ·
          refine ⟨1166041836651974683482503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777361224434649788988335 1166041836651974683482503)
          ·
            refine ⟨1749062754977962025223755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166041836651974683482503 1749062754977962025223755)
            ·
              refine ⟨2623594132466943037835633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749062754977962025223755 2623594132466943037835633)
              ·
                refine ⟨1967695599350207278376725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623594132466943037835633 1967695599350207278376725)
                ·
                  refine ⟨92235731219540966173909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1967695599350207278376725 92235731219540966173909)
                  ·
                    rfl

theorem cell20_202082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_202082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202082 prefixEnd_202082 := by exact prefixLift 202082
  have htrace : WordTrace (prefixWord ++ tailWord_202082) baseStart_202082 baseEnd_202082 := by
    simpa [prefixWord, tailWord_202082, baseEnd_202082] using wordTrace_append hprefix tailTrace_202082
  have hstable : (prefixWord ++ tailWord_202082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202082).length < 2 ^ (prefixWord ++ tailWord_202082).sum := by decide
  have hdescent : baseEnd_202082 < baseStart_202082 := by decide
  rcases family_descends (prefixWord ++ tailWord_202082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202092 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 3]
def baseStart_202092 : Nat := 118140960795 + 202092 * 2 ^ 59
def prefixEnd_202092 : Nat := 4983230072969 + 3 ^ 40 * 202092 * 2
def baseEnd_202092 : Nat := 92240295492025375840535

theorem tailTrace_202092 : CollatzResearch.WordTrace tailWord_202092 prefixEnd_202092 92240295492025375840535 := by
  unfold tailWord_202092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685450391931336705432265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4913933855908448940576353 3685450391931336705432265)
  ·
    refine ⟨2764087793948502529074199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3685450391931336705432265 2764087793948502529074199)
    ·
      refine ⟨4146131690922753793611299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2764087793948502529074199 4146131690922753793611299)
      ·
        refine ⟨6219197536384130690416949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146131690922753793611299 6219197536384130690416949)
        ·
          refine ⟨583049769036012252226589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6219197536384130690416949 583049769036012252226589)
          ·
            refine ⟨218643663388504594584971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 583049769036012252226589 218643663388504594584971)
            ·
              refine ⟨327965495082756891877457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218643663388504594584971 327965495082756891877457)
              ·
                refine ⟨245974121312067668908093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327965495082756891877457 245974121312067668908093)
                ·
                  refine ⟨92240295492025375840535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245974121312067668908093 92240295492025375840535)
                  ·
                    rfl

theorem cell20_202092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_202092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202092 prefixEnd_202092 := by exact prefixLift 202092
  have htrace : WordTrace (prefixWord ++ tailWord_202092) baseStart_202092 baseEnd_202092 := by
    simpa [prefixWord, tailWord_202092, baseEnd_202092] using wordTrace_append hprefix tailTrace_202092
  have hstable : (prefixWord ++ tailWord_202092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202092).length < 2 ^ (prefixWord ++ tailWord_202092).sum := by decide
  have hdescent : baseEnd_202092 < baseStart_202092 := by decide
  rcases family_descends (prefixWord ++ tailWord_202092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202096 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_202096 : Nat := 118140960795 + 202096 * 2 ^ 59
def prefixEnd_202096 : Nat := 4983230072969 + 3 ^ 40 * 202096 * 2
def baseEnd_202096 : Nat := 92242121201019139707185

theorem tailTrace_202096 : CollatzResearch.WordTrace tailWord_202096 prefixEnd_202096 92242121201019139707185 := by
  unfold tailWord_202096
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685523337924091047005071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4914031117232121396006761 3685523337924091047005071)
  ·
    refine ⟨5528285006886136570507607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3685523337924091047005071 5528285006886136570507607)
    ·
      refine ⟨8292427510329204855761411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5528285006886136570507607 8292427510329204855761411)
      ·
        refine ⟨12438641265493807283642117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8292427510329204855761411 12438641265493807283642117)
        ·
          refine ⟨2332245237280088865682897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12438641265493807283642117 2332245237280088865682897)
          ·
            refine ⟨1749183927960066649262173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2332245237280088865682897 1749183927960066649262173)
            ·
              refine ⟨655943972985024993473315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1749183927960066649262173 655943972985024993473315)
              ·
                refine ⟨983915959477537490209973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655943972985024993473315 983915959477537490209973)
                ·
                  refine ⟨92242121201019139707185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 983915959477537490209973 92242121201019139707185)
                  ·
                    rfl

theorem cell20_202096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_202096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202096 prefixEnd_202096 := by exact prefixLift 202096
  have htrace : WordTrace (prefixWord ++ tailWord_202096) baseStart_202096 baseEnd_202096 := by
    simpa [prefixWord, tailWord_202096, baseEnd_202096] using wordTrace_append hprefix tailTrace_202096
  have hstable : (prefixWord ++ tailWord_202096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202096).length < 2 ^ (prefixWord ++ tailWord_202096).sum := by decide
  have hdescent : baseEnd_202096 < baseStart_202096 := by decide
  rcases family_descends (prefixWord ++ tailWord_202096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202120 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_202120 : Nat := 118140960795 + 202120 * 2 ^ 59
def prefixEnd_202120 : Nat := 4983230072969 + 3 ^ 40 * 202120 * 2
def baseEnd_202120 : Nat := 92253075454981722907087

theorem tailTrace_202120 : CollatzResearch.WordTrace tailWord_202120 prefixEnd_202120 92253075454981722907087 := by
  unfold tailWord_202120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685961013880617096441907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4914614685174156128589209 3685961013880617096441907)
  ·
    refine ⟨5528941520820925644662861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3685961013880617096441907 5528941520820925644662861)
    ·
      refine ⟨2073353070307847116748573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5528941520820925644662861 2073353070307847116748573)
      ·
        refine ⟨777507401365442668780715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2073353070307847116748573 777507401365442668780715)
        ·
          refine ⟨1166261102048164003171073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777507401365442668780715 1166261102048164003171073)
          ·
            refine ⟨874695826536123002378305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166261102048164003171073 874695826536123002378305)
            ·
              refine ⟨656021869902092251783729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874695826536123002378305 656021869902092251783729)
              ·
                refine ⟨492016402426569188837797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656021869902092251783729 492016402426569188837797)
                ·
                  refine ⟨92253075454981722907087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492016402426569188837797 92253075454981722907087)
                  ·
                    rfl

theorem cell20_202120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_202120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202120 prefixEnd_202120 := by exact prefixLift 202120
  have htrace : WordTrace (prefixWord ++ tailWord_202120) baseStart_202120 baseEnd_202120 := by
    simpa [prefixWord, tailWord_202120, baseEnd_202120] using wordTrace_append hprefix tailTrace_202120
  have hstable : (prefixWord ++ tailWord_202120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202120).length < 2 ^ (prefixWord ++ tailWord_202120).sum := by decide
  have hdescent : baseEnd_202120 < baseStart_202120 := by decide
  rcases family_descends (prefixWord ++ tailWord_202120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202137 : List Nat := [1, 2, 1, 2, 1, 5, 3, 3, 2]
def baseStart_202137 : Nat := 118140960795 + 202137 * 2 ^ 59
def prefixEnd_202137 : Nat := 4983230072969 + 3 ^ 40 * 202137 * 2
def baseEnd_202137 : Nat := 92260834718205219340351

theorem tailTrace_202137 : CollatzResearch.WordTrace tailWord_202137 prefixEnd_202137 92260834718205219340351 := by
  unfold tailWord_202137
  simp only [CollatzResearch.WordTrace]
  refine ⟨7372542068699646096252665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4915028045799764064168443 7372542068699646096252665)
  ·
    refine ⟨5529406551524734572189499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7372542068699646096252665 5529406551524734572189499)
    ·
      refine ⟨8294109827287101858284249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5529406551524734572189499 8294109827287101858284249)
      ·
        refine ⟨6220582370465326393713187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8294109827287101858284249 6220582370465326393713187)
        ·
          refine ⟨9330873555697989590569781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220582370465326393713187 9330873555697989590569781)
          ·
            refine ⟨874769395846686524115917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9330873555697989590569781 874769395846686524115917)
            ·
              refine ⟨328038523442507446543469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 874769395846686524115917 328038523442507446543469)
              ·
                refine ⟨123014446290940292453801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328038523442507446543469 123014446290940292453801)
                ·
                  refine ⟨92260834718205219340351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123014446290940292453801 92260834718205219340351)
                  ·
                    rfl

theorem cell20_202137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_202137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202137 prefixEnd_202137 := by exact prefixLift 202137
  have htrace : WordTrace (prefixWord ++ tailWord_202137) baseStart_202137 baseEnd_202137 := by
    simpa [prefixWord, tailWord_202137, baseEnd_202137] using wordTrace_append hprefix tailTrace_202137
  have hstable : (prefixWord ++ tailWord_202137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202137).length < 2 ^ (prefixWord ++ tailWord_202137).sum := by decide
  have hdescent : baseEnd_202137 < baseStart_202137 := by decide
  rcases family_descends (prefixWord ++ tailWord_202137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202151 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 3]
def baseStart_202151 : Nat := 118140960795 + 202151 * 2 ^ 59
def prefixEnd_202151 : Nat := 4983230072969 + 3 ^ 40 * 202151 * 2
def baseEnd_202151 : Nat := 92267224699683392873627

theorem tailTrace_202151 : CollatzResearch.WordTrace tailWord_202151 prefixEnd_202151 92267224699683392873627 := by
  unfold tailWord_202151
  simp only [CollatzResearch.WordTrace]
  refine ⟨7373052690648926487262307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4915368460432617658174871 7373052690648926487262307)
  ·
    refine ⟨11059579035973389730893461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7373052690648926487262307 11059579035973389730893461)
    ·
      refine ⟨518417767311252643635631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11059579035973389730893461 518417767311252643635631)
      ·
        refine ⟨777626650966878965453447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518417767311252643635631 777626650966878965453447)
        ·
          refine ⟨1166439976450318448180171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777626650966878965453447 1166439976450318448180171)
          ·
            refine ⟨1749659964675477672270257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166439976450318448180171 1749659964675477672270257)
            ·
              refine ⟨1312244973506608254202693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1749659964675477672270257 1312244973506608254202693)
              ·
                refine ⟨246045932532489047663005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1312244973506608254202693 246045932532489047663005)
                ·
                  refine ⟨92267224699683392873627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246045932532489047663005 92267224699683392873627)
                  ·
                    rfl

theorem cell20_202151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 3].length) (baseStart_202151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202151 prefixEnd_202151 := by exact prefixLift 202151
  have htrace : WordTrace (prefixWord ++ tailWord_202151) baseStart_202151 baseEnd_202151 := by
    simpa [prefixWord, tailWord_202151, baseEnd_202151] using wordTrace_append hprefix tailTrace_202151
  have hstable : (prefixWord ++ tailWord_202151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202151).length < 2 ^ (prefixWord ++ tailWord_202151).sum := by decide
  have hdescent : baseEnd_202151 < baseStart_202151 := by decide
  rcases family_descends (prefixWord ++ tailWord_202151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202165 : List Nat := [1, 3, 3, 2, 2, 1, 1, 7]
def baseStart_202165 : Nat := 118140960795 + 202165 * 2 ^ 59
def prefixEnd_202165 : Nat := 4983230072969 + 3 ^ 40 * 202165 * 2
def baseEnd_202165 : Nat := 30757871560387188802301

theorem tailTrace_202165 : CollatzResearch.WordTrace tailWord_202165 prefixEnd_202165 30757871560387188802301 := by
  unfold tailWord_202165
  simp only [CollatzResearch.WordTrace]
  refine ⟨7373563312598206878271949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4915708875065471252181299 7373563312598206878271949)
  ·
    refine ⟨2765086242224327579351981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7373563312598206878271949 2765086242224327579351981)
    ·
      refine ⟨1036907340834122842256993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2765086242224327579351981 1036907340834122842256993)
      ·
        refine ⟨777680505625592131692745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1036907340834122842256993 777680505625592131692745)
        ·
          refine ⟨583260379219194098769559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 777680505625592131692745 583260379219194098769559)
          ·
            refine ⟨874890568828791148154339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583260379219194098769559 874890568828791148154339)
            ·
              refine ⟨1312335853243186722231509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874890568828791148154339 1312335853243186722231509)
              ·
                refine ⟨30757871560387188802301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1312335853243186722231509 30757871560387188802301)
                ·
                  rfl

theorem cell20_202165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_202165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202165 prefixEnd_202165 := by exact prefixLift 202165
  have htrace : WordTrace (prefixWord ++ tailWord_202165) baseStart_202165 baseEnd_202165 := by
    simpa [prefixWord, tailWord_202165, baseEnd_202165] using wordTrace_append hprefix tailTrace_202165
  have hstable : (prefixWord ++ tailWord_202165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202165).length < 2 ^ (prefixWord ++ tailWord_202165).sum := by decide
  have hdescent : baseEnd_202165 < baseStart_202165 := by decide
  rcases family_descends (prefixWord ++ tailWord_202165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202179 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_202179 : Nat := 118140960795 + 202179 * 2 ^ 59
def prefixEnd_202179 : Nat := 4983230072969 + 3 ^ 40 * 202179 * 2
def baseEnd_202179 : Nat := 92280004662639739940179

theorem tailTrace_202179 : CollatzResearch.WordTrace tailWord_202179 prefixEnd_202179 92280004662639739940179 := by
  unfold tailWord_202179
  simp only [CollatzResearch.WordTrace]
  refine ⟨7374073934547487269281591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4916049289698324846187727 7374073934547487269281591)
  ·
    refine ⟨11061110901821230903922387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7374073934547487269281591 11061110901821230903922387)
    ·
      refine ⟨16591666352731846355883581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11061110901821230903922387 16591666352731846355883581)
      ·
        refine ⟨6221874882274442383456343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16591666352731846355883581 6221874882274442383456343)
        ·
          refine ⟨9332812323411663575184515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6221874882274442383456343 9332812323411663575184515)
          ·
            refine ⟨13999218485117495362776773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9332812323411663575184515 13999218485117495362776773)
            ·
              refine ⟨2624853465959530380520645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13999218485117495362776773 2624853465959530380520645)
              ·
                refine ⟨492160024867411946347621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2624853465959530380520645 492160024867411946347621)
                ·
                  refine ⟨92280004662639739940179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492160024867411946347621 92280004662639739940179)
                  ·
                    rfl

theorem cell20_202179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_202179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202179 prefixEnd_202179 := by exact prefixLift 202179
  have htrace : WordTrace (prefixWord ++ tailWord_202179) baseStart_202179 baseEnd_202179 := by
    simpa [prefixWord, tailWord_202179, baseEnd_202179] using wordTrace_append hprefix tailTrace_202179
  have hstable : (prefixWord ++ tailWord_202179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202179).length < 2 ^ (prefixWord ++ tailWord_202179).sum := by decide
  have hdescent : baseEnd_202179 < baseStart_202179 := by decide
  rcases family_descends (prefixWord ++ tailWord_202179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202272 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_202272 : Nat := 118140960795 + 202272 * 2 ^ 59
def prefixEnd_202272 : Nat := 4983230072969 + 3 ^ 40 * 202272 * 2
def baseEnd_202272 : Nat := 92322452396744749839799

theorem tailTrace_202272 : CollatzResearch.WordTrace tailWord_202272 prefixEnd_202272 92322452396744749839799 := by
  unfold tailWord_202272
  simp only [CollatzResearch.WordTrace]
  refine ⟨3688732961605282076208535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4918310615473709434944713 3688732961605282076208535)
  ·
    refine ⟨5533099442407923114312803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3688732961605282076208535 5533099442407923114312803)
    ·
      refine ⟨8299649163611884671469205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5533099442407923114312803 8299649163611884671469205)
      ·
        refine ⟨389046054544307093975119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8299649163611884671469205 389046054544307093975119)
        ·
          refine ⟨583569081816460640962679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389046054544307093975119 583569081816460640962679)
          ·
            refine ⟨875353622724690961444019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583569081816460640962679 875353622724690961444019)
            ·
              refine ⟨1313030434087036442166029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875353622724690961444019 1313030434087036442166029)
              ·
                refine ⟨492386412782638665812261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1313030434087036442166029 492386412782638665812261)
                ·
                  refine ⟨92322452396744749839799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492386412782638665812261 92322452396744749839799)
                  ·
                    rfl

theorem cell20_202272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_202272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202272 prefixEnd_202272 := by exact prefixLift 202272
  have htrace : WordTrace (prefixWord ++ tailWord_202272) baseStart_202272 baseEnd_202272 := by
    simpa [prefixWord, tailWord_202272, baseEnd_202272] using wordTrace_append hprefix tailTrace_202272
  have hstable : (prefixWord ++ tailWord_202272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202272).length < 2 ^ (prefixWord ++ tailWord_202272).sum := by decide
  have hdescent : baseEnd_202272 < baseStart_202272 := by decide
  rcases family_descends (prefixWord ++ tailWord_202272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202282 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_202282 : Nat := 118140960795 + 202282 * 2 ^ 59
def prefixEnd_202282 : Nat := 4983230072969 + 3 ^ 40 * 202282 * 2
def baseEnd_202282 : Nat := 92327016669229159506425

theorem tailTrace_202282 : CollatzResearch.WordTrace tailWord_202282 prefixEnd_202282 92327016669229159506425 := by
  unfold tailWord_202282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844457663293583965070275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4918553768782890573520733 1844457663293583965070275)
  ·
    refine ⟨2766686494940375947605413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1844457663293583965070275 2766686494940375947605413)
    ·
      refine ⟨518753717801320490176015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2766686494940375947605413 518753717801320490176015)
      ·
        refine ⟨778130576701980735264023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518753717801320490176015 778130576701980735264023)
        ·
          refine ⟨1167195865052971102896035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778130576701980735264023 1167195865052971102896035)
          ·
            refine ⟨1750793797579456654344053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167195865052971102896035 1750793797579456654344053)
            ·
              refine ⟨164136918523074061344755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1750793797579456654344053 164136918523074061344755)
              ·
                refine ⟨246205377784611092017133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164136918523074061344755 246205377784611092017133)
                ·
                  refine ⟨92327016669229159506425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246205377784611092017133 92327016669229159506425)
                  ·
                    rfl

theorem cell20_202282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_202282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202282 prefixEnd_202282 := by exact prefixLift 202282
  have htrace : WordTrace (prefixWord ++ tailWord_202282) baseStart_202282 baseEnd_202282 := by
    simpa [prefixWord, tailWord_202282, baseEnd_202282] using wordTrace_append hprefix tailTrace_202282
  have hstable : (prefixWord ++ tailWord_202282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202282).length < 2 ^ (prefixWord ++ tailWord_202282).sum := by decide
  have hdescent : baseEnd_202282 < baseStart_202282 := by decide
  rcases family_descends (prefixWord ++ tailWord_202282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202296 : List Nat := [2, 1, 2, 1, 4, 4, 2, 4]
def baseStart_202296 : Nat := 118140960795 + 202296 * 2 ^ 59
def prefixEnd_202296 : Nat := 4983230072969 + 3 ^ 40 * 202296 * 2
def baseEnd_202296 : Nat := 30777802216902444346567

theorem tailTrace_202296 : CollatzResearch.WordTrace tailWord_202296 prefixEnd_202296 30777802216902444346567 := by
  unfold tailWord_202296
  simp only [CollatzResearch.WordTrace]
  refine ⟨3689170637561808125645371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4918894183415744167527161 3689170637561808125645371)
  ·
    refine ⟨5533755956342712188468057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3689170637561808125645371 5533755956342712188468057)
    ·
      refine ⟨4150316967257034141351043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5533755956342712188468057 4150316967257034141351043)
      ·
        refine ⟨6225475450885551212026565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4150316967257034141351043 6225475450885551212026565)
        ·
          refine ⟨1167276647041040852254981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6225475450885551212026565 1167276647041040852254981)
          ·
            refine ⟨218864371320195159797809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1167276647041040852254981 218864371320195159797809)
            ·
              refine ⟨164148278490146369848357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218864371320195159797809 164148278490146369848357)
              ·
                refine ⟨30777802216902444346567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164148278490146369848357 30777802216902444346567)
                ·
                  rfl

theorem cell20_202296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_202296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202296 prefixEnd_202296 := by exact prefixLift 202296
  have htrace : WordTrace (prefixWord ++ tailWord_202296) baseStart_202296 baseEnd_202296 := by
    simpa [prefixWord, tailWord_202296, baseEnd_202296] using wordTrace_append hprefix tailTrace_202296
  have hstable : (prefixWord ++ tailWord_202296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202296).length < 2 ^ (prefixWord ++ tailWord_202296).sum := by decide
  have hdescent : baseEnd_202296 < baseStart_202296 := by decide
  rcases family_descends (prefixWord ++ tailWord_202296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202324 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_202324 : Nat := 118140960795 + 202324 * 2 ^ 59
def prefixEnd_202324 : Nat := 4983230072969 + 3 ^ 40 * 202324 * 2
def baseEnd_202324 : Nat := 92346186613663680106253

theorem tailTrace_202324 : CollatzResearch.WordTrace tailWord_202324 prefixEnd_202324 92346186613663680106253 := by
  unfold tailWord_202324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3689681259511088516655013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4919575012681451355540017 3689681259511088516655013)
  ·
    refine ⟨691815236158329096872815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3689681259511088516655013 691815236158329096872815)
    ·
      refine ⟨1037722854237493645309223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 691815236158329096872815 1037722854237493645309223)
      ·
        refine ⟨1556584281356240467963835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037722854237493645309223 1556584281356240467963835)
        ·
          refine ⟨2334876422034360701945753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556584281356240467963835 2334876422034360701945753)
          ·
            refine ⟨1751157316525770526459315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2334876422034360701945753 1751157316525770526459315)
            ·
              refine ⟨2626735974788655789688973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751157316525770526459315 2626735974788655789688973)
              ·
                refine ⟨985025990545745921133365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2626735974788655789688973 985025990545745921133365)
                ·
                  refine ⟨92346186613663680106253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 985025990545745921133365 92346186613663680106253)
                  ·
                    rfl

theorem cell20_202324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_202324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202324 prefixEnd_202324 := by exact prefixLift 202324
  have htrace : WordTrace (prefixWord ++ tailWord_202324) baseStart_202324 baseEnd_202324 := by
    simpa [prefixWord, tailWord_202324, baseEnd_202324] using wordTrace_append hprefix tailTrace_202324
  have hstable : (prefixWord ++ tailWord_202324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202324).length < 2 ^ (prefixWord ++ tailWord_202324).sum := by decide
  have hdescent : baseEnd_202324 < baseStart_202324 := by decide
  rcases family_descends (prefixWord ++ tailWord_202324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202333 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 3]
def baseStart_202333 : Nat := 118140960795 + 202333 * 2 ^ 59
def prefixEnd_202333 : Nat := 4983230072969 + 3 ^ 40 * 202333 * 2
def baseEnd_202333 : Nat := 92350294458899648806217

theorem tailTrace_202333 : CollatzResearch.WordTrace tailWord_202333 prefixEnd_202333 92350294458899648806217 := by
  unfold tailWord_202333
  simp only [CollatzResearch.WordTrace]
  refine ⟨7379690775989571570387653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4919793850659714380258435 7379690775989571570387653)
  ·
    refine ⟨1383692020498044669447685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7379690775989571570387653 1383692020498044669447685)
    ·
      refine ⟨259442253843383375521441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1383692020498044669447685 259442253843383375521441)
      ·
        refine ⟨194581690382537531641081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259442253843383375521441 194581690382537531641081)
        ·
          refine ⟨145936267786903148730811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194581690382537531641081 145936267786903148730811)
          ·
            refine ⟨218904401680354723096217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145936267786903148730811 218904401680354723096217)
            ·
              refine ⟨164178301260266042322163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218904401680354723096217 164178301260266042322163)
              ·
                refine ⟨246267451890399063483245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164178301260266042322163 246267451890399063483245)
                ·
                  refine ⟨92350294458899648806217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246267451890399063483245 92350294458899648806217)
                  ·
                    rfl

theorem cell20_202333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_202333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202333 prefixEnd_202333 := by exact prefixLift 202333
  have htrace : WordTrace (prefixWord ++ tailWord_202333) baseStart_202333 baseEnd_202333 := by
    simpa [prefixWord, tailWord_202333, baseEnd_202333] using wordTrace_append hprefix tailTrace_202333
  have hstable : (prefixWord ++ tailWord_202333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202333).length < 2 ^ (prefixWord ++ tailWord_202333).sum := by decide
  have hdescent : baseEnd_202333 < baseStart_202333 := by decide
  rcases family_descends (prefixWord ++ tailWord_202333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202341 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 3]
def baseStart_202341 : Nat := 118140960795 + 202341 * 2 ^ 59
def prefixEnd_202341 : Nat := 4983230072969 + 3 ^ 40 * 202341 * 2
def baseEnd_202341 : Nat := 92353945876887176539517

theorem tailTrace_202341 : CollatzResearch.WordTrace tailWord_202341 prefixEnd_202341 92353945876887176539517 := by
  unfold tailWord_202341
  simp only [CollatzResearch.WordTrace]
  refine ⟨7379982559960588936678877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4919988373307059291119251 7379982559960588936678877)
  ·
    refine ⟨2767493459985220851254579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7379982559960588936678877 2767493459985220851254579)
    ·
      refine ⟨4151240189977831276881869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2767493459985220851254579 4151240189977831276881869)
      ·
        refine ⟨1556715071241686728830701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4151240189977831276881869 1556715071241686728830701)
        ·
          refine ⟨583768151715632523311513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1556715071241686728830701 583768151715632523311513)
          ·
            refine ⟨437826113786724392483635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583768151715632523311513 437826113786724392483635)
            ·
              refine ⟨656739170680086588725453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437826113786724392483635 656739170680086588725453)
              ·
                refine ⟨246277189005032470772045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656739170680086588725453 246277189005032470772045)
                ·
                  refine ⟨92353945876887176539517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246277189005032470772045 92353945876887176539517)
                  ·
                    rfl

theorem cell20_202341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_202341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202341 prefixEnd_202341 := by exact prefixLift 202341
  have htrace : WordTrace (prefixWord ++ tailWord_202341) baseStart_202341 baseEnd_202341 := by
    simpa [prefixWord, tailWord_202341, baseEnd_202341] using wordTrace_append hprefix tailTrace_202341
  have hstable : (prefixWord ++ tailWord_202341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202341).length < 2 ^ (prefixWord ++ tailWord_202341).sum := by decide
  have hdescent : baseEnd_202341 < baseStart_202341 := by decide
  rcases family_descends (prefixWord ++ tailWord_202341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202382 : List Nat := [4, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_202382 : Nat := 118140960795 + 202382 * 2 ^ 59
def prefixEnd_202382 : Nat := 4983230072969 + 3 ^ 40 * 202382 * 2
def baseEnd_202382 : Nat := 92372659394073256172683

theorem tailTrace_202382 : CollatzResearch.WordTrace tailWord_202382 prefixEnd_202382 92372659394073256172683 := by
  unfold tailWord_202382
  simp only [CollatzResearch.WordTrace]
  refine ⟨922684744101506617365175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4920985301874701959280933 922684744101506617365175)
  ·
    refine ⟨1384027116152259926047763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 922684744101506617365175 1384027116152259926047763)
    ·
      refine ⟨2076040674228389889071645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1384027116152259926047763 2076040674228389889071645)
      ·
        refine ⟨778515252835646208401867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2076040674228389889071645 778515252835646208401867)
        ·
          refine ⟨1167772879253469312602801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778515252835646208401867 1167772879253469312602801)
          ·
            refine ⟨875829659440101984452101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167772879253469312602801 875829659440101984452101)
            ·
              refine ⟨164218061145019122084769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 875829659440101984452101 164218061145019122084769)
              ·
                refine ⟨123163545858764341563577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164218061145019122084769 123163545858764341563577)
                ·
                  refine ⟨92372659394073256172683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123163545858764341563577 92372659394073256172683)
                  ·
                    rfl

theorem cell20_202382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_202382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202382 prefixEnd_202382 := by exact prefixLift 202382
  have htrace : WordTrace (prefixWord ++ tailWord_202382) baseStart_202382 baseEnd_202382 := by
    simpa [prefixWord, tailWord_202382, baseEnd_202382] using wordTrace_append hprefix tailTrace_202382
  have hstable : (prefixWord ++ tailWord_202382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202382).length < 2 ^ (prefixWord ++ tailWord_202382).sum := by decide
  have hdescent : baseEnd_202382 < baseStart_202382 := by decide
  rcases family_descends (prefixWord ++ tailWord_202382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202455 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 3]
def baseStart_202455 : Nat := 118140960795 + 202455 * 2 ^ 59
def prefixEnd_202455 : Nat := 4983230072969 + 3 ^ 40 * 202455 * 2
def baseEnd_202455 : Nat := 92405978583209446739051

theorem tailTrace_202455 : CollatzResearch.WordTrace tailWord_202455 prefixEnd_202455 92405978583209446739051 := by
  unfold tailWord_202455
  simp only [CollatzResearch.WordTrace]
  refine ⟨7384140481547586406328819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4922760321031724270885879 7384140481547586406328819)
  ·
    refine ⟨11076210722321379609493229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7384140481547586406328819 11076210722321379609493229)
    ·
      refine ⟨4153579020870517353559961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11076210722321379609493229 4153579020870517353559961)
      ·
        refine ⟨3115184265652888015169971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4153579020870517353559961 3115184265652888015169971)
        ·
          refine ⟨4672776398479332022754957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115184265652888015169971 4672776398479332022754957)
          ·
            refine ⟨1752291149429749508533109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4672776398479332022754957 1752291149429749508533109)
            ·
              refine ⟨164277295259039016424979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1752291149429749508533109 164277295259039016424979)
              ·
                refine ⟨246415942888558524637469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164277295259039016424979 246415942888558524637469)
                ·
                  refine ⟨92405978583209446739051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246415942888558524637469 92405978583209446739051)
                  ·
                    rfl

theorem cell20_202455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 3].length) (baseStart_202455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202455 prefixEnd_202455 := by exact prefixLift 202455
  have htrace : WordTrace (prefixWord ++ tailWord_202455) baseStart_202455 baseEnd_202455 := by
    simpa [prefixWord, tailWord_202455, baseEnd_202455] using wordTrace_append hprefix tailTrace_202455
  have hstable : (prefixWord ++ tailWord_202455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202455).length < 2 ^ (prefixWord ++ tailWord_202455).sum := by decide
  have hdescent : baseEnd_202455 < baseStart_202455 := by decide
  rcases family_descends (prefixWord ++ tailWord_202455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202465 : List Nat := [1, 2, 3, 1, 6, 1, 2, 4]
def baseStart_202465 : Nat := 118140960795 + 202465 * 2 ^ 59
def prefixEnd_202465 : Nat := 4983230072969 + 3 ^ 40 * 202465 * 2
def baseEnd_202465 : Nat := 30803514285231285468559

theorem tailTrace_202465 : CollatzResearch.WordTrace tailWord_202465 prefixEnd_202465 30803514285231285468559 := by
  unfold tailWord_202465
  simp only [CollatzResearch.WordTrace]
  refine ⟨7384505211511358114192849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4923003474340905409461899 7384505211511358114192849)
  ·
    refine ⟨5538378908633518585644637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7384505211511358114192849 5538378908633518585644637)
    ·
      refine ⟨2076892090737569469616739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5538378908633518585644637 2076892090737569469616739)
      ·
        refine ⟨3115338136106354204425109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2076892090737569469616739 3115338136106354204425109)
        ·
          refine ⟨146031475129985353332427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3115338136106354204425109 146031475129985353332427)
          ·
            refine ⟨219047212694978029998641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146031475129985353332427 219047212694978029998641)
            ·
              refine ⟨164285409521233522498981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219047212694978029998641 164285409521233522498981)
              ·
                refine ⟨30803514285231285468559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164285409521233522498981 30803514285231285468559)
                ·
                  rfl

theorem cell20_202465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 4].length) (baseStart_202465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202465 prefixEnd_202465 := by exact prefixLift 202465
  have htrace : WordTrace (prefixWord ++ tailWord_202465) baseStart_202465 baseEnd_202465 := by
    simpa [prefixWord, tailWord_202465, baseEnd_202465] using wordTrace_append hprefix tailTrace_202465
  have hstable : (prefixWord ++ tailWord_202465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202465).length < 2 ^ (prefixWord ++ tailWord_202465).sum := by decide
  have hdescent : baseEnd_202465 < baseStart_202465 := by decide
  rcases family_descends (prefixWord ++ tailWord_202465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202500 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_202500 : Nat := 118140960795 + 202500 * 2 ^ 59
def prefixEnd_202500 : Nat := 4983230072969 + 3 ^ 40 * 202500 * 2
def baseEnd_202500 : Nat := 92426517809389290238867

theorem tailTrace_202500 : CollatzResearch.WordTrace tailWord_202500 prefixEnd_202500 92426517809389290238867 := by
  unfold tailWord_202500
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692890883192279545858477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4923854510923039394477969 3692890883192279545858477)
  ·
    refine ⟨1384834081197104829696929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3692890883192279545858477 1384834081197104829696929)
    ·
      refine ⟨1038625560897828622272697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1384834081197104829696929 1038625560897828622272697)
      ·
        refine ⟨778969170673371466704523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1038625560897828622272697 778969170673371466704523)
        ·
          refine ⟨1168453756010057200056785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778969170673371466704523 1168453756010057200056785)
          ·
            refine ⟨876340317007542900042589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168453756010057200056785 876340317007542900042589)
            ·
              refine ⟨328627618877828587515971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 876340317007542900042589 328627618877828587515971)
              ·
                refine ⟨492941428316742881273957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328627618877828587515971 492941428316742881273957)
                ·
                  refine ⟨92426517809389290238867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492941428316742881273957 92426517809389290238867)
                  ·
                    rfl

theorem cell20_202500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_202500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202500 prefixEnd_202500 := by exact prefixLift 202500
  have htrace : WordTrace (prefixWord ++ tailWord_202500) baseStart_202500 baseEnd_202500 := by
    simpa [prefixWord, tailWord_202500, baseEnd_202500] using wordTrace_append hprefix tailTrace_202500
  have hstable : (prefixWord ++ tailWord_202500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202500).length < 2 ^ (prefixWord ++ tailWord_202500).sum := by decide
  have hdescent : baseEnd_202500 < baseStart_202500 := by decide
  rcases family_descends (prefixWord ++ tailWord_202500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202528 : List Nat := [2, 1, 1, 5, 1, 1, 1, 8]
def baseStart_202528 : Nat := 118140960795 + 202528 * 2 ^ 59
def prefixEnd_202528 : Nat := 4983230072969 + 3 ^ 40 * 202528 * 2
def baseEnd_202528 : Nat := 30813099257448545768473

theorem tailTrace_202528 : CollatzResearch.WordTrace tailWord_202528 prefixEnd_202528 30813099257448545768473 := by
  unfold tailWord_202528
  simp only [CollatzResearch.WordTrace]
  refine ⟨3693401505141559936868119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4924535340188746582490825 3693401505141559936868119)
  ·
    refine ⟨5540102257712339905302179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3693401505141559936868119 5540102257712339905302179)
    ·
      refine ⟨8310153386568509857953269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5540102257712339905302179 8310153386568509857953269)
      ·
        refine ⟨779076879990797799183119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8310153386568509857953269 779076879990797799183119)
        ·
          refine ⟨1168615319986196698774679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779076879990797799183119 1168615319986196698774679)
          ·
            refine ⟨1752922979979295048162019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168615319986196698774679 1752922979979295048162019)
            ·
              refine ⟨2629384469968942572243029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752922979979295048162019 2629384469968942572243029)
              ·
                refine ⟨30813099257448545768473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2629384469968942572243029 30813099257448545768473)
                ·
                  rfl

theorem cell20_202528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_202528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202528 prefixEnd_202528 := by exact prefixLift 202528
  have htrace : WordTrace (prefixWord ++ tailWord_202528) baseStart_202528 baseEnd_202528 := by
    simpa [prefixWord, tailWord_202528, baseEnd_202528] using wordTrace_append hprefix tailTrace_202528
  have hstable : (prefixWord ++ tailWord_202528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202528).length < 2 ^ (prefixWord ++ tailWord_202528).sum := by decide
  have hdescent : baseEnd_202528 < baseStart_202528 := by decide
  rcases family_descends (prefixWord ++ tailWord_202528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202548 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 3]
def baseStart_202548 : Nat := 118140960795 + 202548 * 2 ^ 59
def prefixEnd_202548 : Nat := 4983230072969 + 3 ^ 40 * 202548 * 2
def baseEnd_202548 : Nat := 92448426317314456638671

theorem tailTrace_202548 : CollatzResearch.WordTrace tailWord_202548 prefixEnd_202548 92448426317314456638671 := by
  unfold tailWord_202548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3693766235105331644732149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4925021646807108859642865 3693766235105331644732149)
  ·
    refine ⟨346290584541124841693639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3693766235105331644732149 346290584541124841693639)
    ·
      refine ⟨519435876811687262540459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346290584541124841693639 519435876811687262540459)
      ·
        refine ⟨779153815217530893810689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519435876811687262540459 779153815217530893810689)
        ·
          refine ⟨584365361413148170358017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 779153815217530893810689 584365361413148170358017)
          ·
            refine ⟨438274021059861127768513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584365361413148170358017 438274021059861127768513)
            ·
              refine ⟨328705515794895845826385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438274021059861127768513 328705515794895845826385)
              ·
                refine ⟨246529136846171884369789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328705515794895845826385 246529136846171884369789)
                ·
                  refine ⟨92448426317314456638671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246529136846171884369789 92448426317314456638671)
                  ·
                    rfl

theorem cell20_202548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_202548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202548 prefixEnd_202548 := by exact prefixLift 202548
  have htrace : WordTrace (prefixWord ++ tailWord_202548) baseStart_202548 baseEnd_202548 := by
    simpa [prefixWord, tailWord_202548, baseEnd_202548] using wordTrace_append hprefix tailTrace_202548
  have hstable : (prefixWord ++ tailWord_202548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202548).length < 2 ^ (prefixWord ++ tailWord_202548).sum := by decide
  have hdescent : baseEnd_202548 < baseStart_202548 := by decide
  rcases family_descends (prefixWord ++ tailWord_202548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202552 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 3]
def baseStart_202552 : Nat := 118140960795 + 202552 * 2 ^ 59
def prefixEnd_202552 : Nat := 4983230072969 + 3 ^ 40 * 202552 * 2
def baseEnd_202552 : Nat := 92450252026308220505321

theorem tailTrace_202552 : CollatzResearch.WordTrace tailWord_202552 prefixEnd_202552 92450252026308220505321 := by
  unfold tailWord_202552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3693839181098085986304955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4925118908130781315073273 3693839181098085986304955)
  ·
    refine ⟨5540758771647128979457433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3693839181098085986304955 5540758771647128979457433)
    ·
      refine ⟨4155569078735346734593075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5540758771647128979457433 4155569078735346734593075)
      ·
        refine ⟨6233353618103020101889613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4155569078735346734593075 6233353618103020101889613)
        ·
          refine ⟨2337507606788632538208605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6233353618103020101889613 2337507606788632538208605)
          ·
            refine ⟨876565352545737201828227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2337507606788632538208605 876565352545737201828227)
            ·
              refine ⟨1314848028818605802742341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876565352545737201828227 1314848028818605802742341)
              ·
                refine ⟨246534005403488588014189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1314848028818605802742341 246534005403488588014189)
                ·
                  refine ⟨92450252026308220505321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246534005403488588014189 92450252026308220505321)
                  ·
                    rfl

theorem cell20_202552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_202552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202552 prefixEnd_202552 := by exact prefixLift 202552
  have htrace : WordTrace (prefixWord ++ tailWord_202552) baseStart_202552 baseEnd_202552 := by
    simpa [prefixWord, tailWord_202552, baseEnd_202552] using wordTrace_append hprefix tailTrace_202552
  have hstable : (prefixWord ++ tailWord_202552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202552).length < 2 ^ (prefixWord ++ tailWord_202552).sum := by decide
  have hdescent : baseEnd_202552 < baseStart_202552 := by decide
  rcases family_descends (prefixWord ++ tailWord_202552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202604 : List Nat := [2, 2, 1, 1, 4, 3, 7]
def baseStart_202604 : Nat := 118140960795 + 202604 * 2 ^ 59
def prefixEnd_202604 : Nat := 4983230072969 + 3 ^ 40 * 202604 * 2
def baseEnd_202604 : Nat := 10274887360358572307975

theorem tailTrace_202604 : CollatzResearch.WordTrace tailWord_202604 prefixEnd_202604 10274887360358572307975 := by
  unfold tailWord_202604
  simp only [CollatzResearch.WordTrace]
  refine ⟨3694787479003892426751433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4926383305338523235668577 3694787479003892426751433)
  ·
    refine ⟨2771090609252919320063575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3694787479003892426751433 2771090609252919320063575)
    ·
      refine ⟨4156635913879378980095363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2771090609252919320063575 4156635913879378980095363)
      ·
        refine ⟨6234953870819068470143045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4156635913879378980095363 6234953870819068470143045)
        ·
          refine ⟨1169053850778575338151821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6234953870819068470143045 1169053850778575338151821)
          ·
            refine ⟨438395194041965751806933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1169053850778575338151821 438395194041965751806933)
            ·
              refine ⟨10274887360358572307975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 438395194041965751806933 10274887360358572307975)
              ·
                rfl

theorem cell20_202604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 7].length) (baseStart_202604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202604 prefixEnd_202604 := by exact prefixLift 202604
  have htrace : WordTrace (prefixWord ++ tailWord_202604) baseStart_202604 baseEnd_202604 := by
    simpa [prefixWord, tailWord_202604, baseEnd_202604] using wordTrace_append hprefix tailTrace_202604
  have hstable : (prefixWord ++ tailWord_202604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202604).length < 2 ^ (prefixWord ++ tailWord_202604).sum := by decide
  have hdescent : baseEnd_202604 < baseStart_202604 := by decide
  rcases family_descends (prefixWord ++ tailWord_202604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202628 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 3]
def baseStart_202628 : Nat := 118140960795 + 202628 * 2 ^ 59
def prefixEnd_202628 : Nat := 4983230072969 + 3 ^ 40 * 202628 * 2
def baseEnd_202628 : Nat := 92484940497189733971677

theorem tailTrace_202628 : CollatzResearch.WordTrace tailWord_202628 prefixEnd_202628 92484940497189733971677 := by
  unfold tailWord_202628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3695225154960418476188269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4926966873280557968251025 3695225154960418476188269)
  ·
    refine ⟨1385709433110156928570601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3695225154960418476188269 1385709433110156928570601)
    ·
      refine ⟨1039282074832617696427951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1385709433110156928570601 1039282074832617696427951)
      ·
        refine ⟨1558923112248926544641927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039282074832617696427951 1558923112248926544641927)
        ·
          refine ⟨2338384668373389816962891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558923112248926544641927 2338384668373389816962891)
          ·
            refine ⟨3507577002560084725444337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338384668373389816962891 3507577002560084725444337)
            ·
              refine ⟨2630682751920063544083253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3507577002560084725444337 2630682751920063544083253)
              ·
                refine ⟨246626507992505957257805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2630682751920063544083253 246626507992505957257805)
                ·
                  refine ⟨92484940497189733971677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246626507992505957257805 92484940497189733971677)
                  ·
                    rfl

theorem cell20_202628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_202628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202628 prefixEnd_202628 := by exact prefixLift 202628
  have htrace : WordTrace (prefixWord ++ tailWord_202628) baseStart_202628 baseEnd_202628 := by
    simpa [prefixWord, tailWord_202628, baseEnd_202628] using wordTrace_append hprefix tailTrace_202628
  have hstable : (prefixWord ++ tailWord_202628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202628).length < 2 ^ (prefixWord ++ tailWord_202628).sum := by decide
  have hdescent : baseEnd_202628 < baseStart_202628 := by decide
  rcases family_descends (prefixWord ++ tailWord_202628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202638 : List Nat := [4, 1, 1, 5, 1, 1, 1, 6]
def baseStart_202638 : Nat := 118140960795 + 202638 * 2 ^ 59
def prefixEnd_202638 : Nat := 4983230072969 + 3 ^ 40 * 202638 * 2
def baseEnd_202638 : Nat := 30829834923224714546101

theorem tailTrace_202638 : CollatzResearch.WordTrace tailWord_202638 prefixEnd_202638 30829834923224714546101 := by
  unfold tailWord_202638
  simp only [CollatzResearch.WordTrace]
  refine ⟨923851879985576082530071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4927210026589739106827045 923851879985576082530071)
  ·
    refine ⟨1385777819978364123795107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 923851879985576082530071 1385777819978364123795107)
    ·
      refine ⟨2078666729967546185692661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1385777819978364123795107 2078666729967546185692661)
      ·
        refine ⟨194875005934457454908687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2078666729967546185692661 194875005934457454908687)
        ·
          refine ⟨292312508901686182363031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194875005934457454908687 292312508901686182363031)
          ·
            refine ⟨438468763352529273544547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292312508901686182363031 438468763352529273544547)
            ·
              refine ⟨657703145028793910316821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438468763352529273544547 657703145028793910316821)
              ·
                refine ⟨30829834923224714546101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 657703145028793910316821 30829834923224714546101)
                ·
                  rfl

theorem cell20_202638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_202638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202638 prefixEnd_202638 := by exact prefixLift 202638
  have htrace : WordTrace (prefixWord ++ tailWord_202638) baseStart_202638 baseEnd_202638 := by
    simpa [prefixWord, tailWord_202638, baseEnd_202638] using wordTrace_append hprefix tailTrace_202638
  have hstable : (prefixWord ++ tailWord_202638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202638).length < 2 ^ (prefixWord ++ tailWord_202638).sum := by decide
  have hdescent : baseEnd_202638 < baseStart_202638 := by decide
  rcases family_descends (prefixWord ++ tailWord_202638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202649 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_202649 : Nat := 118140960795 + 202649 * 2 ^ 59
def prefixEnd_202649 : Nat := 4983230072969 + 3 ^ 40 * 202649 * 2
def baseEnd_202649 : Nat := 92494525469406994271591

theorem tailTrace_202649 : CollatzResearch.WordTrace tailWord_202649 prefixEnd_202649 92494525469406994271591 := by
  unfold tailWord_202649
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391216242844757538891001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4927477495229838359260667 7391216242844757538891001)
  ·
    refine ⟨5543412182133568154168251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7391216242844757538891001 5543412182133568154168251)
    ·
      refine ⟨8315118273200352231252377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5543412182133568154168251 8315118273200352231252377)
      ·
        refine ⟨6236338704900264173439283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8315118273200352231252377 6236338704900264173439283)
        ·
          refine ⟨9354508057350396260158925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6236338704900264173439283 9354508057350396260158925)
          ·
            refine ⟨3507940521506398597559597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9354508057350396260158925 3507940521506398597559597)
            ·
              refine ⟨1315477695564899474084849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3507940521506398597559597 1315477695564899474084849)
              ·
                refine ⟨986608271673674605563637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315477695564899474084849 986608271673674605563637)
                ·
                  refine ⟨92494525469406994271591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 986608271673674605563637 92494525469406994271591)
                  ·
                    rfl

theorem cell20_202649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_202649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202649 prefixEnd_202649 := by exact prefixLift 202649
  have htrace : WordTrace (prefixWord ++ tailWord_202649) baseStart_202649 baseEnd_202649 := by
    simpa [prefixWord, tailWord_202649, baseEnd_202649] using wordTrace_append hprefix tailTrace_202649
  have hstable : (prefixWord ++ tailWord_202649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202649).length < 2 ^ (prefixWord ++ tailWord_202649).sum := by decide
  have hdescent : baseEnd_202649 < baseStart_202649 := by decide
  rcases family_descends (prefixWord ++ tailWord_202649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202680 : List Nat := [2, 1, 2, 1, 2, 3, 4, 5]
def baseStart_202680 : Nat := 118140960795 + 202680 * 2 ^ 59
def prefixEnd_202680 : Nat := 4983230072969 + 3 ^ 40 * 202680 * 2
def baseEnd_202680 : Nat := 30836224904702888079377

theorem tailTrace_202680 : CollatzResearch.WordTrace tailWord_202680 prefixEnd_202680 30836224904702888079377 := by
  unfold tailWord_202680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3696173452866224916634747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4928231270488299888846329 3696173452866224916634747)
  ·
    refine ⟨5544260179299337374952121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3696173452866224916634747 5544260179299337374952121)
    ·
      refine ⟨4158195134474503031214091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5544260179299337374952121 4158195134474503031214091)
      ·
        refine ⟨6237292701711754546821137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4158195134474503031214091 6237292701711754546821137)
        ·
          refine ⟨4677969526283815910115853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6237292701711754546821137 4677969526283815910115853)
          ·
            refine ⟨1754238572356430966293445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4677969526283815910115853 1754238572356430966293445)
            ·
              refine ⟨328919732316830806180021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1754238572356430966293445 328919732316830806180021)
              ·
                refine ⟨30836224904702888079377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 328919732316830806180021 30836224904702888079377)
                ·
                  rfl

theorem cell20_202680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_202680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202680 prefixEnd_202680 := by exact prefixLift 202680
  have htrace : WordTrace (prefixWord ++ tailWord_202680) baseStart_202680 baseEnd_202680 := by
    simpa [prefixWord, tailWord_202680, baseEnd_202680] using wordTrace_append hprefix tailTrace_202680
  have hstable : (prefixWord ++ tailWord_202680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202680).length < 2 ^ (prefixWord ++ tailWord_202680).sum := by decide
  have hdescent : baseEnd_202680 < baseStart_202680 := by decide
  rcases family_descends (prefixWord ++ tailWord_202680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202732 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_202732 : Nat := 118140960795 + 202732 * 2 ^ 59
def prefixEnd_202732 : Nat := 4983230072969 + 3 ^ 40 * 202732 * 2
def baseEnd_202732 : Nat := 92532408931027594504585

theorem tailTrace_202732 : CollatzResearch.WordTrace tailWord_202732 prefixEnd_202732 92532408931027594504585 := by
  unfold tailWord_202732
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697121750772031357081225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4929495667696041809441633 3697121750772031357081225)
  ·
    refine ⟨2772841313079023517810919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3697121750772031357081225 2772841313079023517810919)
    ·
      refine ⟨4159261969618535276716379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2772841313079023517810919 4159261969618535276716379)
      ·
        refine ⟨6238892954427802915074569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4159261969618535276716379 6238892954427802915074569)
        ·
          refine ⟨4679169715820852186305927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6238892954427802915074569 4679169715820852186305927)
          ·
            refine ⟨7018754573731278279458891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679169715820852186305927 7018754573731278279458891)
            ·
              refine ⟨10528131860596917419188337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018754573731278279458891 10528131860596917419188337)
              ·
                refine ⟨7896098895447688064391253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10528131860596917419188337 7896098895447688064391253)
                ·
                  refine ⟨92532408931027594504585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7896098895447688064391253 92532408931027594504585)
                  ·
                    rfl

theorem cell20_202732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_202732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202732 prefixEnd_202732 := by exact prefixLift 202732
  have htrace : WordTrace (prefixWord ++ tailWord_202732) baseStart_202732 baseEnd_202732 := by
    simpa [prefixWord, tailWord_202732, baseEnd_202732] using wordTrace_append hprefix tailTrace_202732
  have hstable : (prefixWord ++ tailWord_202732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202732).length < 2 ^ (prefixWord ++ tailWord_202732).sum := by decide
  have hdescent : baseEnd_202732 < baseStart_202732 := by decide
  rcases family_descends (prefixWord ++ tailWord_202732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202763 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_202763 : Nat := 118140960795 + 202763 * 2 ^ 59
def prefixEnd_202763 : Nat := 4983230072969 + 3 ^ 40 * 202763 * 2
def baseEnd_202763 : Nat := 92546558175729264471125

theorem tailTrace_202763 : CollatzResearch.WordTrace tailWord_202763 prefixEnd_202763 92546558175729264471125 := by
  unfold tailWord_202763
  simp only [CollatzResearch.WordTrace]
  refine ⟨7395374164431755008540943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4930249442954503339027295 7395374164431755008540943)
  ·
    refine ⟨11093061246647632512811415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7395374164431755008540943 11093061246647632512811415)
    ·
      refine ⟨16639591869971448769217123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11093061246647632512811415 16639591869971448769217123)
      ·
        refine ⟨24959387804957173153825685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16639591869971448769217123 24959387804957173153825685)
        ·
          refine ⟨1169971303357367491585579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24959387804957173153825685 1169971303357367491585579)
          ·
            refine ⟨1754956955036051237378369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169971303357367491585579 1754956955036051237378369)
            ·
              refine ⟨1316217716277038428033777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1754956955036051237378369 1316217716277038428033777)
              ·
                refine ⟨987163287207778821025333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316217716277038428033777 987163287207778821025333)
                ·
                  refine ⟨92546558175729264471125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 987163287207778821025333 92546558175729264471125)
                  ·
                    rfl

theorem cell20_202763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_202763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202763 prefixEnd_202763 := by exact prefixLift 202763
  have htrace : WordTrace (prefixWord ++ tailWord_202763) baseStart_202763 baseEnd_202763 := by
    simpa [prefixWord, tailWord_202763, baseEnd_202763] using wordTrace_append hprefix tailTrace_202763
  have hstable : (prefixWord ++ tailWord_202763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202763).length < 2 ^ (prefixWord ++ tailWord_202763).sum := by decide
  have hdescent : baseEnd_202763 < baseStart_202763 := by decide
  rcases family_descends (prefixWord ++ tailWord_202763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202772 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 3]
def baseStart_202772 : Nat := 118140960795 + 202772 * 2 ^ 59
def prefixEnd_202772 : Nat := 4983230072969 + 3 ^ 40 * 202772 * 2
def baseEnd_202772 : Nat := 92550666020965233171089

theorem tailTrace_202772 : CollatzResearch.WordTrace tailWord_202772 prefixEnd_202772 92550666020965233171089 := by
  unfold tailWord_202772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697851210699574772809285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4930468280932766363745713 3697851210699574772809285)
  ·
    refine ⟨693347102006170269901741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3697851210699574772809285 693347102006170269901741)
    ·
      refine ⟨260005163252313851213153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 693347102006170269901741 260005163252313851213153)
      ·
        refine ⟨195003872439235388409865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260005163252313851213153 195003872439235388409865)
        ·
          refine ⟨146252904329426541307399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195003872439235388409865 146252904329426541307399)
          ·
            refine ⟨219379356494139811961099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146252904329426541307399 219379356494139811961099)
            ·
              refine ⟨329069034741209717941649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219379356494139811961099 329069034741209717941649)
              ·
                refine ⟨246801776055907288456237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329069034741209717941649 246801776055907288456237)
                ·
                  refine ⟨92550666020965233171089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246801776055907288456237 92550666020965233171089)
                  ·
                    rfl

theorem cell20_202772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_202772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202772 prefixEnd_202772 := by exact prefixLift 202772
  have htrace : WordTrace (prefixWord ++ tailWord_202772) baseStart_202772 baseEnd_202772 := by
    simpa [prefixWord, tailWord_202772, baseEnd_202772] using wordTrace_append hprefix tailTrace_202772
  have hstable : (prefixWord ++ tailWord_202772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202772).length < 2 ^ (prefixWord ++ tailWord_202772).sum := by decide
  have hdescent : baseEnd_202772 < baseStart_202772 := by decide
  rcases family_descends (prefixWord ++ tailWord_202772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202780 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_202780 : Nat := 118140960795 + 202780 * 2 ^ 59
def prefixEnd_202780 : Nat := 4983230072969 + 3 ^ 40 * 202780 * 2
def baseEnd_202780 : Nat := 92554317438952760904389

theorem tailTrace_202780 : CollatzResearch.WordTrace tailWord_202780 prefixEnd_202780 92554317438952760904389 := by
  unfold tailWord_202780
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697997102685083455954897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4930662803580111274606529 3697997102685083455954897)
  ·
    refine ⟨2773497827013812591966173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3697997102685083455954897 2773497827013812591966173)
    ·
      refine ⟨1040061685130179721987315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2773497827013812591966173 1040061685130179721987315)
      ·
        refine ⟨1560092527695269582980973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040061685130179721987315 1560092527695269582980973)
        ·
          refine ⟨585034697885726093617865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1560092527695269582980973 585034697885726093617865)
          ·
            refine ⟨438776023414294570213399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585034697885726093617865 438776023414294570213399)
            ·
              refine ⟨658164035121441855320099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438776023414294570213399 658164035121441855320099)
              ·
                refine ⟨987246052682162782980149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658164035121441855320099 987246052682162782980149)
                ·
                  refine ⟨92554317438952760904389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 987246052682162782980149 92554317438952760904389)
                  ·
                    rfl

theorem cell20_202780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_202780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202780 prefixEnd_202780 := by exact prefixLift 202780
  have htrace : WordTrace (prefixWord ++ tailWord_202780) baseStart_202780 baseEnd_202780 := by
    simpa [prefixWord, tailWord_202780, baseEnd_202780] using wordTrace_append hprefix tailTrace_202780
  have hstable : (prefixWord ++ tailWord_202780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202780).length < 2 ^ (prefixWord ++ tailWord_202780).sum := by decide
  have hdescent : baseEnd_202780 < baseStart_202780 := by decide
  rcases family_descends (prefixWord ++ tailWord_202780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202787 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 4]
def baseStart_202787 : Nat := 118140960795 + 202787 * 2 ^ 59
def prefixEnd_202787 : Nat := 4983230072969 + 3 ^ 40 * 202787 * 2
def baseEnd_202787 : Nat := 92557512429691847671027

theorem tailTrace_202787 : CollatzResearch.WordTrace tailWord_202787 prefixEnd_202787 92557512429691847671027 := by
  unfold tailWord_202787
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396249516344807107414615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4930833010896538071609743 7396249516344807107414615)
  ·
    refine ⟨11094374274517210661121923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7396249516344807107414615 11094374274517210661121923)
    ·
      refine ⟨16641561411775815991682885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11094374274517210661121923 16641561411775815991682885)
      ·
        refine ⟨3120292764707965498440541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16641561411775815991682885 3120292764707965498440541)
        ·
          refine ⟨1170109786765487061915203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3120292764707965498440541 1170109786765487061915203)
          ·
            refine ⟨1755164680148230592872805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170109786765487061915203 1755164680148230592872805)
            ·
              refine ⟨329093377527793236163651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1755164680148230592872805 329093377527793236163651)
              ·
                refine ⟨493640066291689854245477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329093377527793236163651 493640066291689854245477)
                ·
                  refine ⟨92557512429691847671027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493640066291689854245477 92557512429691847671027)
                  ·
                    rfl

theorem cell20_202787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_202787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202787 prefixEnd_202787 := by exact prefixLift 202787
  have htrace : WordTrace (prefixWord ++ tailWord_202787) baseStart_202787 baseEnd_202787 := by
    simpa [prefixWord, tailWord_202787, baseEnd_202787] using wordTrace_append hprefix tailTrace_202787
  have hstable : (prefixWord ++ tailWord_202787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202787).length < 2 ^ (prefixWord ++ tailWord_202787).sum := by decide
  have hdescent : baseEnd_202787 < baseStart_202787 := by decide
  rcases family_descends (prefixWord ++ tailWord_202787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202838 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_202838 : Nat := 118140960795 + 202838 * 2 ^ 59
def prefixEnd_202838 : Nat := 4983230072969 + 3 ^ 40 * 202838 * 2
def baseEnd_202838 : Nat := 92580790219362336970819

theorem tailTrace_202838 : CollatzResearch.WordTrace tailWord_202838 prefixEnd_202838 92580790219362336970819 := by
  unfold tailWord_202838
  simp only [CollatzResearch.WordTrace]
  refine ⟨462381852447502676095073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4932073092773361878347445 462381852447502676095073)
  ·
    refine ⟨346786389335627007071305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 462381852447502676095073 346786389335627007071305)
    ·
      refine ⟨260089792001720255303479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346786389335627007071305 260089792001720255303479)
      ·
        refine ⟨390134688002580382955219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260089792001720255303479 390134688002580382955219)
        ·
          refine ⟨585202032003870574432829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390134688002580382955219 585202032003870574432829)
          ·
            refine ⟨219450762001451465412311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585202032003870574432829 219450762001451465412311)
            ·
              refine ⟨329176143002177198118467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219450762001451465412311 329176143002177198118467)
              ·
                refine ⟨493764214503265797177701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329176143002177198118467 493764214503265797177701)
                ·
                  refine ⟨92580790219362336970819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493764214503265797177701 92580790219362336970819)
                  ·
                    rfl

theorem cell20_202838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_202838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202838 prefixEnd_202838 := by exact prefixLift 202838
  have htrace : WordTrace (prefixWord ++ tailWord_202838) baseStart_202838 baseEnd_202838 := by
    simpa [prefixWord, tailWord_202838, baseEnd_202838] using wordTrace_append hprefix tailTrace_202838
  have hstable : (prefixWord ++ tailWord_202838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202838).length < 2 ^ (prefixWord ++ tailWord_202838).sum := by decide
  have hdescent : baseEnd_202838 < baseStart_202838 := by decide
  rcases family_descends (prefixWord ++ tailWord_202838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202839 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_202839 : Nat := 118140960795 + 202839 * 2 ^ 59
def prefixEnd_202839 : Nat := 4983230072969 + 3 ^ 40 * 202839 * 2
def baseEnd_202839 : Nat := 92581246646610777937481

theorem tailTrace_202839 : CollatzResearch.WordTrace tailWord_202839 prefixEnd_202839 92581246646610777937481 := by
  unfold tailWord_202839
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398146112156419988307571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4932097408104279992205047 7398146112156419988307571)
  ·
    refine ⟨11097219168234629982461357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7398146112156419988307571 11097219168234629982461357)
    ·
      refine ⟨4161457188087986243423009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11097219168234629982461357 4161457188087986243423009)
      ·
        refine ⟨3121092891065989682567257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4161457188087986243423009 3121092891065989682567257)
        ·
          refine ⟨2340819668299492261925443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3121092891065989682567257 2340819668299492261925443)
          ·
            refine ⟨3511229502449238392888165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340819668299492261925443 3511229502449238392888165)
            ·
              refine ⟨658355531709232198666531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3511229502449238392888165 658355531709232198666531)
              ·
                refine ⟨987533297563848297999797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658355531709232198666531 987533297563848297999797)
                ·
                  refine ⟨92581246646610777937481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 987533297563848297999797 92581246646610777937481)
                  ·
                    rfl

theorem cell20_202839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_202839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202839 prefixEnd_202839 := by exact prefixLift 202839
  have htrace : WordTrace (prefixWord ++ tailWord_202839) baseStart_202839 baseEnd_202839 := by
    simpa [prefixWord, tailWord_202839, baseEnd_202839] using wordTrace_append hprefix tailTrace_202839
  have hstable : (prefixWord ++ tailWord_202839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202839).length < 2 ^ (prefixWord ++ tailWord_202839).sum := by decide
  have hdescent : baseEnd_202839 < baseStart_202839 := by decide
  rcases family_descends (prefixWord ++ tailWord_202839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202904 : List Nat := [2, 1, 2, 4, 4, 1, 1, 5]
def baseStart_202904 : Nat := 118140960795 + 202904 * 2 ^ 59
def prefixEnd_202904 : Nat := 4983230072969 + 3 ^ 40 * 202904 * 2
def baseEnd_202904 : Nat := 30870304805919813590183

theorem tailTrace_202904 : CollatzResearch.WordTrace tailWord_202904 prefixEnd_202904 30870304805919813590183 := by
  unfold tailWord_202904
  simp only [CollatzResearch.WordTrace]
  refine ⟨3700258428460468044711883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4933677904613957392949177 3700258428460468044711883)
  ·
    refine ⟨5550387642690702067067825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3700258428460468044711883 5550387642690702067067825)
    ·
      refine ⟨4162790732018026550300869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5550387642690702067067825 4162790732018026550300869)
      ·
        refine ⟨780523262253379978181413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4162790732018026550300869 780523262253379978181413)
        ·
          refine ⟨146348111672508745909015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 780523262253379978181413 146348111672508745909015)
          ·
            refine ⟨219522167508763118863523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146348111672508745909015 219522167508763118863523)
            ·
              refine ⟨329283251263144678295285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219522167508763118863523 329283251263144678295285)
              ·
                refine ⟨30870304805919813590183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 329283251263144678295285 30870304805919813590183)
                ·
                  rfl

theorem cell20_202904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_202904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202904 prefixEnd_202904 := by exact prefixLift 202904
  have htrace : WordTrace (prefixWord ++ tailWord_202904) baseStart_202904 baseEnd_202904 := by
    simpa [prefixWord, tailWord_202904, baseEnd_202904] using wordTrace_append hprefix tailTrace_202904
  have hstable : (prefixWord ++ tailWord_202904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202904).length < 2 ^ (prefixWord ++ tailWord_202904).sum := by decide
  have hdescent : baseEnd_202904 < baseStart_202904 := by decide
  rcases family_descends (prefixWord ++ tailWord_202904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202945 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 3]
def baseStart_202945 : Nat := 118140960795 + 202945 * 2 ^ 59
def prefixEnd_202945 : Nat := 4983230072969 + 3 ^ 40 * 202945 * 2
def baseEnd_202945 : Nat := 92629627934945520403715

theorem tailTrace_202945 : CollatzResearch.WordTrace tailWord_202945 prefixEnd_202945 92629627934945520403715 := by
  unfold tailWord_202945
  simp only [CollatzResearch.WordTrace]
  refine ⟨7402012249772400091666289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4934674833181600061110859 7402012249772400091666289)
  ·
    refine ⟨5551509187329300068749717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7402012249772400091666289 5551509187329300068749717)
    ·
      refine ⟨260226993156060940722643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5551509187329300068749717 260226993156060940722643)
      ·
        refine ⟨390340489734091411083965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260226993156060940722643 390340489734091411083965)
        ·
          refine ⟨146377683650284279156487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390340489734091411083965 146377683650284279156487)
          ·
            refine ⟨219566525475426418734731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146377683650284279156487 219566525475426418734731)
            ·
              refine ⟨329349788213139628102097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219566525475426418734731 329349788213139628102097)
              ·
                refine ⟨247012341159854721076573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329349788213139628102097 247012341159854721076573)
                ·
                  refine ⟨92629627934945520403715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247012341159854721076573 92629627934945520403715)
                  ·
                    rfl

theorem cell20_202945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_202945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202945 prefixEnd_202945 := by exact prefixLift 202945
  have htrace : WordTrace (prefixWord ++ tailWord_202945) baseStart_202945 baseEnd_202945 := by
    simpa [prefixWord, tailWord_202945, baseEnd_202945] using wordTrace_append hprefix tailTrace_202945
  have hstable : (prefixWord ++ tailWord_202945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202945).length < 2 ^ (prefixWord ++ tailWord_202945).sum := by decide
  have hdescent : baseEnd_202945 < baseStart_202945 := by decide
  rcases family_descends (prefixWord ++ tailWord_202945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202953 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 3]
def baseStart_202953 : Nat := 118140960795 + 202953 * 2 ^ 59
def prefixEnd_202953 : Nat := 4983230072969 + 3 ^ 40 * 202953 * 2
def baseEnd_202953 : Nat := 92633279352933048137015

theorem tailTrace_202953 : CollatzResearch.WordTrace tailWord_202953 prefixEnd_202953 92633279352933048137015 := by
  unfold tailWord_202953
  simp only [CollatzResearch.WordTrace]
  refine ⟨7402304033743417457957513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4934869355828944971971675 7402304033743417457957513)
  ·
    refine ⟨5551728025307563093468135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7402304033743417457957513 5551728025307563093468135)
    ·
      refine ⟨8327592037961344640202203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5551728025307563093468135 8327592037961344640202203)
      ·
        refine ⟨12491388056942016960303305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8327592037961344640202203 12491388056942016960303305)
        ·
          refine ⟨9368541042706512720227479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12491388056942016960303305 9368541042706512720227479)
          ·
            refine ⟨14052811564059769080341219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9368541042706512720227479 14052811564059769080341219)
            ·
              refine ⟨21079217346089653620511829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14052811564059769080341219 21079217346089653620511829)
              ·
                refine ⟨247022078274488128365373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 21079217346089653620511829 247022078274488128365373)
                ·
                  refine ⟨92633279352933048137015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247022078274488128365373 92633279352933048137015)
                  ·
                    rfl

theorem cell20_202953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_202953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202953 prefixEnd_202953 := by exact prefixLift 202953
  have htrace : WordTrace (prefixWord ++ tailWord_202953) baseStart_202953 baseEnd_202953 := by
    simpa [prefixWord, tailWord_202953, baseEnd_202953] using wordTrace_append hprefix tailTrace_202953
  have hstable : (prefixWord ++ tailWord_202953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202953).length < 2 ^ (prefixWord ++ tailWord_202953).sum := by decide
  have hdescent : baseEnd_202953 < baseStart_202953 := by decide
  rcases family_descends (prefixWord ++ tailWord_202953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202967 : List Nat := [1, 1, 3, 2, 1, 2, 1, 9]
def baseStart_202967 : Nat := 118140960795 + 202967 * 2 ^ 59
def prefixEnd_202967 : Nat := 4983230072969 + 3 ^ 40 * 202967 * 2
def baseEnd_202967 : Nat := 30879889778137073890097

theorem tailTrace_202967 : CollatzResearch.WordTrace tailWord_202967 prefixEnd_202967 30879889778137073890097 := by
  unfold tailWord_202967
  simp only [CollatzResearch.WordTrace]
  refine ⟨7402814655692697848967155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4935209770461798565978103 7402814655692697848967155)
  ·
    refine ⟨11104221983539046773450733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7402814655692697848967155 11104221983539046773450733)
    ·
      refine ⟨4164083243827142540044025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11104221983539046773450733 4164083243827142540044025)
      ·
        refine ⟨3123062432870356905033019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4164083243827142540044025 3123062432870356905033019)
        ·
          refine ⟨4684593649305535357549529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3123062432870356905033019 4684593649305535357549529)
          ·
            refine ⟨3513445236979151518162147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4684593649305535357549529 3513445236979151518162147)
            ·
              refine ⟨5270167855468727277243221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3513445236979151518162147 5270167855468727277243221)
              ·
                refine ⟨30879889778137073890097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5270167855468727277243221 30879889778137073890097)
                ·
                  rfl

theorem cell20_202967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_202967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202967 prefixEnd_202967 := by exact prefixLift 202967
  have htrace : WordTrace (prefixWord ++ tailWord_202967) baseStart_202967 baseEnd_202967 := by
    simpa [prefixWord, tailWord_202967, baseEnd_202967] using wordTrace_append hprefix tailTrace_202967
  have hstable : (prefixWord ++ tailWord_202967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202967).length < 2 ^ (prefixWord ++ tailWord_202967).sum := by decide
  have hdescent : baseEnd_202967 < baseStart_202967 := by decide
  rcases family_descends (prefixWord ++ tailWord_202967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202984 : List Nat := [2, 1, 4, 1, 2, 3, 1, 6]
def baseStart_202984 : Nat := 118140960795 + 202984 * 2 ^ 59
def prefixEnd_202984 : Nat := 4983230072969 + 3 ^ 40 * 202984 * 2
def baseEnd_202984 : Nat := 30882476199211572701185

theorem tailTrace_202984 : CollatzResearch.WordTrace tailWord_202984 prefixEnd_202984 30882476199211572701185 := by
  unfold tailWord_202984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701717348315554876168003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4935623131087406501557337 3701717348315554876168003)
  ·
    refine ⟨5552576022473332314252005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3701717348315554876168003 5552576022473332314252005)
    ·
      refine ⟨1041108004213749808922251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5552576022473332314252005 1041108004213749808922251)
      ·
        refine ⟨1561662006320624713383377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041108004213749808922251 1561662006320624713383377)
        ·
          refine ⟨1171246504740468535037533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1561662006320624713383377 1171246504740468535037533)
          ·
            refine ⟨439217439277675700639075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1171246504740468535037533 439217439277675700639075)
            ·
              refine ⟨658826158916513550958613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439217439277675700639075 658826158916513550958613)
              ·
                refine ⟨30882476199211572701185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 658826158916513550958613 30882476199211572701185)
                ·
                  rfl

theorem cell20_202984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_202984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202984 prefixEnd_202984 := by exact prefixLift 202984
  have htrace : WordTrace (prefixWord ++ tailWord_202984) baseStart_202984 baseEnd_202984 := by
    simpa [prefixWord, tailWord_202984, baseEnd_202984] using wordTrace_append hprefix tailTrace_202984
  have hstable : (prefixWord ++ tailWord_202984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202984).length < 2 ^ (prefixWord ++ tailWord_202984).sum := by decide
  have hdescent : baseEnd_202984 < baseStart_202984 := by decide
  rcases family_descends (prefixWord ++ tailWord_202984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202991 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_202991 : Nat := 118140960795 + 202991 * 2 ^ 59
def prefixEnd_202991 : Nat := 4983230072969 + 3 ^ 40 * 202991 * 2
def baseEnd_202991 : Nat := 92650623588373804870193

theorem tailTrace_202991 : CollatzResearch.WordTrace tailWord_202991 prefixEnd_202991 92650623588373804870193 := by
  unfold tailWord_202991
  simp only [CollatzResearch.WordTrace]
  refine ⟨7403690007605749947840827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4935793338403833298560551 7403690007605749947840827)
  ·
    refine ⟨11105535011408624921761241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7403690007605749947840827 11105535011408624921761241)
    ·
      refine ⟨8329151258556468691320931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11105535011408624921761241 8329151258556468691320931)
      ·
        refine ⟨12493726887834703036981397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8329151258556468691320931 12493726887834703036981397)
        ·
          refine ⟨585643447867251704858503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12493726887834703036981397 585643447867251704858503)
          ·
            refine ⟨878465171800877557287755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585643447867251704858503 878465171800877557287755)
            ·
              refine ⟨1317697757701316335931633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878465171800877557287755 1317697757701316335931633)
              ·
                refine ⟨988273318275987251948725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317697757701316335931633 988273318275987251948725)
                ·
                  refine ⟨92650623588373804870193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 988273318275987251948725 92650623588373804870193)
                  ·
                    rfl

theorem cell20_202991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_202991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_202991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_202991 prefixEnd_202991 := by exact prefixLift 202991
  have htrace : WordTrace (prefixWord ++ tailWord_202991) baseStart_202991 baseEnd_202991 := by
    simpa [prefixWord, tailWord_202991, baseEnd_202991] using wordTrace_append hprefix tailTrace_202991
  have hstable : (prefixWord ++ tailWord_202991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202991).length < 2 ^ (prefixWord ++ tailWord_202991).sum := by decide
  have hdescent : baseEnd_202991 < baseStart_202991 := by decide
  rcases family_descends (prefixWord ++ tailWord_202991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203022 : List Nat := [4, 1, 1, 2, 1, 2, 4, 5]
def baseStart_203022 : Nat := 118140960795 + 203022 * 2 ^ 59
def prefixEnd_203022 : Nat := 4983230072969 + 3 ^ 40 * 203022 * 2
def baseEnd_203022 : Nat := 30888257611025158278911

theorem tailTrace_203022 : CollatzResearch.WordTrace tailWord_203022 prefixEnd_203022 30888257611025158278911 := by
  unfold tailWord_203022
  simp only [CollatzResearch.WordTrace]
  refine ⟨925602583811680280277415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4936547113662294828146213 925602583811680280277415)
  ·
    refine ⟨1388403875717520420416123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 925602583811680280277415 1388403875717520420416123)
    ·
      refine ⟨2082605813576280630624185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1388403875717520420416123 2082605813576280630624185)
      ·
        refine ⟨1561954360182210472968139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2082605813576280630624185 1561954360182210472968139)
        ·
          refine ⟨2342931540273315709452209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1561954360182210472968139 2342931540273315709452209)
          ·
            refine ⟨1757198655204986782089157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2342931540273315709452209 1757198655204986782089157)
            ·
              refine ⟨329474747850935021641717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1757198655204986782089157 329474747850935021641717)
              ·
                refine ⟨30888257611025158278911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 329474747850935021641717 30888257611025158278911)
                ·
                  rfl

theorem cell20_203022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_203022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203022 prefixEnd_203022 := by exact prefixLift 203022
  have htrace : WordTrace (prefixWord ++ tailWord_203022) baseStart_203022 baseEnd_203022 := by
    simpa [prefixWord, tailWord_203022, baseEnd_203022] using wordTrace_append hprefix tailTrace_203022
  have hstable : (prefixWord ++ tailWord_203022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203022).length < 2 ^ (prefixWord ++ tailWord_203022).sum := by decide
  have hdescent : baseEnd_203022 < baseStart_203022 := by decide
  rcases family_descends (prefixWord ++ tailWord_203022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203025 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 3]
def baseStart_203025 : Nat := 118140960795 + 203025 * 2 ^ 59
def prefixEnd_203025 : Nat := 4983230072969 + 3 ^ 40 * 203025 * 2
def baseEnd_203025 : Nat := 92666142114820797736721

theorem tailTrace_203025 : CollatzResearch.WordTrace tailWord_203025 prefixEnd_203025 92666142114820797736721 := by
  unfold tailWord_203025
  simp only [CollatzResearch.WordTrace]
  refine ⟨7404930089482573754578529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4936620059655049169719019 7404930089482573754578529)
  ·
    refine ⟨5553697567111930315933897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7404930089482573754578529 5553697567111930315933897)
    ·
      refine ⟨4165273175333947736950423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5553697567111930315933897 4165273175333947736950423)
      ·
        refine ⟨6247909763000921605425635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165273175333947736950423 6247909763000921605425635)
        ·
          refine ⟨9371864644501382408138453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247909763000921605425635 9371864644501382408138453)
          ·
            refine ⟨219653077605501150190745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9371864644501382408138453 219653077605501150190745)
            ·
              refine ⟨164739808204125862643059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219653077605501150190745 164739808204125862643059)
              ·
                refine ⟨247109712306188793964589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164739808204125862643059 247109712306188793964589)
                ·
                  refine ⟨92666142114820797736721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247109712306188793964589 92666142114820797736721)
                  ·
                    rfl

theorem cell20_203025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_203025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203025 prefixEnd_203025 := by exact prefixLift 203025
  have htrace : WordTrace (prefixWord ++ tailWord_203025) baseStart_203025 baseEnd_203025 := by
    simpa [prefixWord, tailWord_203025, baseEnd_203025] using wordTrace_append hprefix tailTrace_203025
  have hstable : (prefixWord ++ tailWord_203025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203025).length < 2 ^ (prefixWord ++ tailWord_203025).sum := by decide
  have hdescent : baseEnd_203025 < baseStart_203025 := by decide
  rcases family_descends (prefixWord ++ tailWord_203025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203036 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_203036 : Nat := 118140960795 + 203036 * 2 ^ 59
def prefixEnd_203036 : Nat := 4983230072969 + 3 ^ 40 * 203036 * 2
def baseEnd_203036 : Nat := 92671162814553648370009

theorem tailTrace_203036 : CollatzResearch.WordTrace tailWord_203036 prefixEnd_203036 92671162814553648370009 := by
  unfold tailWord_203036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3702665646221361316614481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4936887528295148422152641 3702665646221361316614481)
  ·
    refine ⟨2776999234666020987460861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3702665646221361316614481 2776999234666020987460861)
    ·
      refine ⟨1041374712999757870297823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2776999234666020987460861 1041374712999757870297823)
      ·
        refine ⟨1562062069499636805446735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041374712999757870297823 1562062069499636805446735)
        ·
          refine ⟨2343093104249455208170103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562062069499636805446735 2343093104249455208170103)
          ·
            refine ⟨3514639656374182812255155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343093104249455208170103 3514639656374182812255155)
            ·
              refine ⟨5271959484561274218382733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514639656374182812255155 5271959484561274218382733)
              ·
                refine ⟨1976984806710477831893525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5271959484561274218382733 1976984806710477831893525)
                ·
                  refine ⟨92671162814553648370009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1976984806710477831893525 92671162814553648370009)
                  ·
                    rfl

theorem cell20_203036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_203036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203036 prefixEnd_203036 := by exact prefixLift 203036
  have htrace : WordTrace (prefixWord ++ tailWord_203036) baseStart_203036 baseEnd_203036 := by
    simpa [prefixWord, tailWord_203036, baseEnd_203036] using wordTrace_append hprefix tailTrace_203036
  have hstable : (prefixWord ++ tailWord_203036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203036).length < 2 ^ (prefixWord ++ tailWord_203036).sum := by decide
  have hdescent : baseEnd_203036 < baseStart_203036 := by decide
  rcases family_descends (prefixWord ++ tailWord_203036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203043 : List Nat := [1, 1, 1, 4, 2, 2, 1, 8]
def baseStart_203043 : Nat := 118140960795 + 203043 * 2 ^ 59
def prefixEnd_203043 : Nat := 4983230072969 + 3 ^ 40 * 203043 * 2
def baseEnd_203043 : Nat := 30891452601764245045549

theorem tailTrace_203043 : CollatzResearch.WordTrace tailWord_203043 prefixEnd_203043 30891452601764245045549 := by
  unfold tailWord_203043
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405586603417362828733783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4937057735611575219155855 7405586603417362828733783)
  ·
    refine ⟨11108379905126044243100675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7405586603417362828733783 11108379905126044243100675)
    ·
      refine ⟨16662569857689066364651013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11108379905126044243100675 16662569857689066364651013)
      ·
        refine ⟨3124231848316699943372065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16662569857689066364651013 3124231848316699943372065)
        ·
          refine ⟨2343173886237524957529049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3124231848316699943372065 2343173886237524957529049)
          ·
            refine ⟨1757380414678143718146787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2343173886237524957529049 1757380414678143718146787)
            ·
              refine ⟨2636070622017215577220181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757380414678143718146787 2636070622017215577220181)
              ·
                refine ⟨30891452601764245045549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2636070622017215577220181 30891452601764245045549)
                ·
                  rfl

theorem cell20_203043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_203043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203043 prefixEnd_203043 := by exact prefixLift 203043
  have htrace : WordTrace (prefixWord ++ tailWord_203043) baseStart_203043 baseEnd_203043 := by
    simpa [prefixWord, tailWord_203043, baseEnd_203043] using wordTrace_append hprefix tailTrace_203043
  have hstable : (prefixWord ++ tailWord_203043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203043).length < 2 ^ (prefixWord ++ tailWord_203043).sum := by decide
  have hdescent : baseEnd_203043 < baseStart_203043 := by decide
  rcases family_descends (prefixWord ++ tailWord_203043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203060 : List Nat := [2, 5, 1, 1, 1, 10]
def baseStart_203060 : Nat := 118140960795 + 203060 * 2 ^ 59
def prefixEnd_203060 : Nat := 4983230072969 + 3 ^ 40 * 203060 * 2
def baseEnd_203060 : Nat := 3432671002537638206293

theorem tailTrace_203060 : CollatzResearch.WordTrace tailWord_203060 prefixEnd_203060 3432671002537638206293 := by
  unfold tailWord_203060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703103322177887366051317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4937471096237183154735089 3703103322177887366051317)
  ·
    refine ⟨347165936454176940567311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3703103322177887366051317 347165936454176940567311)
    ·
      refine ⟨520748904681265410850967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347165936454176940567311 520748904681265410850967)
      ·
        refine ⟨781123357021898116276451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520748904681265410850967 781123357021898116276451)
        ·
          refine ⟨1171685035532847174414677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781123357021898116276451 1171685035532847174414677)
          ·
            refine ⟨3432671002537638206293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1171685035532847174414677 3432671002537638206293)
            ·
              rfl

theorem cell20_203060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 10].length) (baseStart_203060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203060 prefixEnd_203060 := by exact prefixLift 203060
  have htrace : WordTrace (prefixWord ++ tailWord_203060) baseStart_203060 baseEnd_203060 := by
    simpa [prefixWord, tailWord_203060, baseEnd_203060] using wordTrace_append hprefix tailTrace_203060
  have hstable : (prefixWord ++ tailWord_203060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203060).length < 2 ^ (prefixWord ++ tailWord_203060).sum := by decide
  have hdescent : baseEnd_203060 < baseStart_203060 := by decide
  rcases family_descends (prefixWord ++ tailWord_203060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203108 : List Nat := [2, 3, 1, 1, 3, 1, 4, 3, 2]
def baseStart_203108 : Nat := 118140960795 + 203108 * 2 ^ 59
def prefixEnd_203108 : Nat := 4983230072969 + 3 ^ 40 * 203108 * 2
def baseEnd_203108 : Nat := 92704025576441397969715

theorem tailTrace_203108 : CollatzResearch.WordTrace tailWord_203108 prefixEnd_203108 92704025576441397969715 := by
  unfold tailWord_203108
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703978674090939464924989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4938638232121252619899985 3703978674090939464924989)
  ·
    refine ⟨1388992002784102299346871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3703978674090939464924989 1388992002784102299346871)
    ·
      refine ⟨2083488004176153449020307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1388992002784102299346871 2083488004176153449020307)
      ·
        refine ⟨3125232006264230173530461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083488004176153449020307 3125232006264230173530461)
        ·
          refine ⟨1171962002349086315073923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3125232006264230173530461 1171962002349086315073923)
          ·
            refine ⟨1757943003523629472610885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171962002349086315073923 1757943003523629472610885)
            ·
              refine ⟨329614313160680526114541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1757943003523629472610885 329614313160680526114541)
              ·
                refine ⟨123605367435255197292953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329614313160680526114541 123605367435255197292953)
                ·
                  refine ⟨92704025576441397969715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123605367435255197292953 92704025576441397969715)
                  ·
                    rfl

theorem cell20_203108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_203108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203108 prefixEnd_203108 := by exact prefixLift 203108
  have htrace : WordTrace (prefixWord ++ tailWord_203108) baseStart_203108 baseEnd_203108 := by
    simpa [prefixWord, tailWord_203108, baseEnd_203108] using wordTrace_append hprefix tailTrace_203108
  have hstable : (prefixWord ++ tailWord_203108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203108).length < 2 ^ (prefixWord ++ tailWord_203108).sum := by decide
  have hdescent : baseEnd_203108 < baseStart_203108 := by decide
  rcases family_descends (prefixWord ++ tailWord_203108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203122 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_203122 : Nat := 118140960795 + 203122 * 2 ^ 59
def prefixEnd_203122 : Nat := 4983230072969 + 3 ^ 40 * 203122 * 2
def baseEnd_203122 : Nat := 92710415557919571502991

theorem tailTrace_203122 : CollatzResearch.WordTrace tailWord_203122 prefixEnd_203122 92710415557919571502991 := by
  unfold tailWord_203122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1852116992532789830214905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4938978646754106213906413 1852116992532789830214905)
  ·
    refine ⟨1389087744399592372661179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1852116992532789830214905 1389087744399592372661179)
    ·
      refine ⟨2083631616599388558991769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1389087744399592372661179 2083631616599388558991769)
      ·
        refine ⟨1562723712449541419243827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2083631616599388558991769 1562723712449541419243827)
        ·
          refine ⟨2344085568674312128865741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562723712449541419243827 2344085568674312128865741)
          ·
            refine ⟨879032088252867048324653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2344085568674312128865741 879032088252867048324653)
            ·
              refine ⟨329637033094825143121745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 879032088252867048324653 329637033094825143121745)
              ·
                refine ⟨247227774821118857341309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329637033094825143121745 247227774821118857341309)
                ·
                  refine ⟨92710415557919571502991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247227774821118857341309 92710415557919571502991)
                  ·
                    rfl

theorem cell20_203122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_203122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203122 prefixEnd_203122 := by exact prefixLift 203122
  have htrace : WordTrace (prefixWord ++ tailWord_203122) baseStart_203122 baseEnd_203122 := by
    simpa [prefixWord, tailWord_203122, baseEnd_203122] using wordTrace_append hprefix tailTrace_203122
  have hstable : (prefixWord ++ tailWord_203122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203122).length < 2 ^ (prefixWord ++ tailWord_203122).sum := by decide
  have hdescent : baseEnd_203122 < baseStart_203122 := by decide
  rcases family_descends (prefixWord ++ tailWord_203122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203139 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 3]
def baseStart_203139 : Nat := 118140960795 + 203139 * 2 ^ 59
def prefixEnd_203139 : Nat := 4983230072969 + 3 ^ 40 * 203139 * 2
def baseEnd_203139 : Nat := 92718174821143067936255

theorem tailTrace_203139 : CollatzResearch.WordTrace tailWord_203139 prefixEnd_203139 92718174821143067936255 := by
  unfold tailWord_203139
  simp only [CollatzResearch.WordTrace]
  refine ⟨7409088011069571224228471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4939392007379714149485647 7409088011069571224228471)
  ·
    refine ⟨11113632016604356836342707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7409088011069571224228471 11113632016604356836342707)
    ·
      refine ⟨16670448024906535254514061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11113632016604356836342707 16670448024906535254514061)
      ·
        refine ⟨6251418009339950720442773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16670448024906535254514061 6251418009339950720442773)
        ·
          refine ⟨293035219187810190020755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6251418009339950720442773 293035219187810190020755)
          ·
            refine ⟨439552828781715285031133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293035219187810190020755 439552828781715285031133)
            ·
              refine ⟨164832310793143231886675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 439552828781715285031133 164832310793143231886675)
              ·
                refine ⟨247248466189714847830013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164832310793143231886675 247248466189714847830013)
                ·
                  refine ⟨92718174821143067936255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247248466189714847830013 92718174821143067936255)
                  ·
                    rfl

theorem cell20_203139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 3].length) (baseStart_203139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203139 prefixEnd_203139 := by exact prefixLift 203139
  have htrace : WordTrace (prefixWord ++ tailWord_203139) baseStart_203139 baseEnd_203139 := by
    simpa [prefixWord, tailWord_203139, baseEnd_203139] using wordTrace_append hprefix tailTrace_203139
  have hstable : (prefixWord ++ tailWord_203139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203139).length < 2 ^ (prefixWord ++ tailWord_203139).sum := by decide
  have hdescent : baseEnd_203139 < baseStart_203139 := by decide
  rcases family_descends (prefixWord ++ tailWord_203139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203243 : List Nat := [1, 1, 1, 1, 2, 3, 5, 4, 2]
def baseStart_203243 : Nat := 118140960795 + 203243 * 2 ^ 59
def prefixEnd_203243 : Nat := 4983230072969 + 3 ^ 40 * 203243 * 2
def baseEnd_203243 : Nat := 92765643254980928469163

theorem tailTrace_203243 : CollatzResearch.WordTrace tailWord_203243 prefixEnd_203243 92765643254980928469163 := by
  unfold tailWord_203243
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412881202692796986014383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4941920801795197990676255 7412881202692796986014383)
  ·
    refine ⟨11119321804039195479021575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7412881202692796986014383 11119321804039195479021575)
    ·
      refine ⟨16678982706058793218532363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11119321804039195479021575 16678982706058793218532363)
      ·
        refine ⟨25018474059088189827798545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16678982706058793218532363 25018474059088189827798545)
        ·
          refine ⟨18763855544316142370848909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25018474059088189827798545 18763855544316142370848909)
          ·
            refine ⟨7036445829118553389068341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18763855544316142370848909 7036445829118553389068341)
            ·
              refine ⟨659666796479864380225157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7036445829118553389068341 659666796479864380225157)
              ·
                refine ⟨123687524339974571292217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 659666796479864380225157 123687524339974571292217)
                ·
                  refine ⟨92765643254980928469163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123687524339974571292217 92765643254980928469163)
                  ·
                    rfl

theorem cell20_203243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 2].length) (baseStart_203243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203243 prefixEnd_203243 := by exact prefixLift 203243
  have htrace : WordTrace (prefixWord ++ tailWord_203243) baseStart_203243 baseEnd_203243 := by
    simpa [prefixWord, tailWord_203243, baseEnd_203243] using wordTrace_append hprefix tailTrace_203243
  have hstable : (prefixWord ++ tailWord_203243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203243).length < 2 ^ (prefixWord ++ tailWord_203243).sum := by decide
  have hdescent : baseEnd_203243 < baseStart_203243 := by decide
  rcases family_descends (prefixWord ++ tailWord_203243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203257 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 3]
def baseStart_203257 : Nat := 118140960795 + 203257 * 2 ^ 59
def prefixEnd_203257 : Nat := 4983230072969 + 3 ^ 40 * 203257 * 2
def baseEnd_203257 : Nat := 92772033236459102002439

theorem tailTrace_203257 : CollatzResearch.WordTrace tailWord_203257 prefixEnd_203257 92772033236459102002439 := by
  unfold tailWord_203257
  simp only [CollatzResearch.WordTrace]
  refine ⟨7413391824642077377024025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4942261216428051584682683 7413391824642077377024025)
  ·
    refine ⟨5560043868481558032768019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7413391824642077377024025 5560043868481558032768019)
    ·
      refine ⟨8340065802722337049152029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5560043868481558032768019 8340065802722337049152029)
      ·
        refine ⟨3127524676020876393432011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8340065802722337049152029 3127524676020876393432011)
        ·
          refine ⟨4691287014031314590148017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3127524676020876393432011 4691287014031314590148017)
          ·
            refine ⟨3518465260523485942611013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4691287014031314590148017 3518465260523485942611013)
            ·
              refine ⟨659712236348153614239565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3518465260523485942611013 659712236348153614239565)
              ·
                refine ⟨247392088630557605339837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 659712236348153614239565 247392088630557605339837)
                ·
                  refine ⟨92772033236459102002439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247392088630557605339837 92772033236459102002439)
                  ·
                    rfl

theorem cell20_203257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_203257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203257 prefixEnd_203257 := by exact prefixLift 203257
  have htrace : WordTrace (prefixWord ++ tailWord_203257) baseStart_203257 baseEnd_203257 := by
    simpa [prefixWord, tailWord_203257, baseEnd_203257] using wordTrace_append hprefix tailTrace_203257
  have hstable : (prefixWord ++ tailWord_203257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203257).length < 2 ^ (prefixWord ++ tailWord_203257).sum := by decide
  have hdescent : baseEnd_203257 < baseStart_203257 := by decide
  rcases family_descends (prefixWord ++ tailWord_203257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203323 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_203323 : Nat := 118140960795 + 203323 * 2 ^ 59
def prefixEnd_203323 : Nat := 4983230072969 + 3 ^ 40 * 203323 * 2
def baseEnd_203323 : Nat := 92802157434856205802169

theorem tailTrace_203323 : CollatzResearch.WordTrace tailWord_203323 prefixEnd_203323 92802157434856205802169 := by
  unfold tailWord_203323
  simp only [CollatzResearch.WordTrace]
  refine ⟨7415799042402970648926623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4943866028268647099284415 7415799042402970648926623)
  ·
    refine ⟨11123698563604455973389935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7415799042402970648926623 11123698563604455973389935)
    ·
      refine ⟨16685547845406683960084903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11123698563604455973389935 16685547845406683960084903)
      ·
        refine ⟨25028321768110025940127355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16685547845406683960084903 25028321768110025940127355)
        ·
          refine ⟨37542482652165038910191033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25028321768110025940127355 37542482652165038910191033)
          ·
            refine ⟨28156861989123779182643275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37542482652165038910191033 28156861989123779182643275)
            ·
              refine ⟨42235292983685668773964913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28156861989123779182643275 42235292983685668773964913)
              ·
                refine ⟨31676469737764251580473685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42235292983685668773964913 31676469737764251580473685)
                ·
                  refine ⟨92802157434856205802169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 31676469737764251580473685 92802157434856205802169)
                  ·
                    rfl

theorem cell20_203323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_203323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203323 prefixEnd_203323 := by exact prefixLift 203323
  have htrace : WordTrace (prefixWord ++ tailWord_203323) baseStart_203323 baseEnd_203323 := by
    simpa [prefixWord, tailWord_203323, baseEnd_203323] using wordTrace_append hprefix tailTrace_203323
  have hstable : (prefixWord ++ tailWord_203323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203323).length < 2 ^ (prefixWord ++ tailWord_203323).sum := by decide
  have hdescent : baseEnd_203323 < baseStart_203323 := by decide
  rcases family_descends (prefixWord ++ tailWord_203323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203385 : List Nat := [1, 2, 1, 3, 3, 2, 2, 6]
def baseStart_203385 : Nat := 118140960795 + 203385 * 2 ^ 59
def prefixEnd_203385 : Nat := 4983230072969 + 3 ^ 40 * 203385 * 2
def baseEnd_203385 : Nat := 30943485308086515245083

theorem tailTrace_203385 : CollatzResearch.WordTrace tailWord_203385 prefixEnd_203385 30943485308086515245083 := by
  unfold tailWord_203385
  simp only [CollatzResearch.WordTrace]
  refine ⟨7418060368178355237683609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4945373578785570158455739 7418060368178355237683609)
  ·
    refine ⟨5563545276133766428262707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7418060368178355237683609 5563545276133766428262707)
    ·
      refine ⟨8345317914200649642394061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5563545276133766428262707 8345317914200649642394061)
      ·
        refine ⟨3129494217825243615897773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8345317914200649642394061 3129494217825243615897773)
        ·
          refine ⟨1173560331684466355961665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3129494217825243615897773 1173560331684466355961665)
          ·
            refine ⟨880170248763349766971249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173560331684466355961665 880170248763349766971249)
            ·
              refine ⟨660127686572512325228437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880170248763349766971249 660127686572512325228437)
              ·
                refine ⟨30943485308086515245083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 660127686572512325228437 30943485308086515245083)
                ·
                  rfl

theorem cell20_203385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_203385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203385 prefixEnd_203385 := by exact prefixLift 203385
  have htrace : WordTrace (prefixWord ++ tailWord_203385) baseStart_203385 baseEnd_203385 := by
    simpa [prefixWord, tailWord_203385, baseEnd_203385] using wordTrace_append hprefix tailTrace_203385
  have hstable : (prefixWord ++ tailWord_203385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203385).length < 2 ^ (prefixWord ++ tailWord_203385).sum := by decide
  have hdescent : baseEnd_203385 < baseStart_203385 := by decide
  rcases family_descends (prefixWord ++ tailWord_203385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203402 : List Nat := [3, 1, 2, 3, 4, 7]
def baseStart_203402 : Nat := 118140960795 + 203402 * 2 ^ 59
def prefixEnd_203402 : Nat := 4983230072969 + 3 ^ 40 * 203402 * 2
def baseEnd_203402 : Nat := 3438452414351223784019

theorem tailTrace_203402 : CollatzResearch.WordTrace tailWord_203402 prefixEnd_203402 3438452414351223784019 := by
  unfold tailWord_203402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1854670102279191785263115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4945786939411178094034973 1854670102279191785263115)
  ·
    refine ⟨2782005153418787677894673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1854670102279191785263115 2782005153418787677894673)
    ·
      refine ⟨2086503865064090758421005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2782005153418787677894673 2086503865064090758421005)
      ·
        refine ⟨782438949399034034407877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2086503865064090758421005 782438949399034034407877)
        ·
          refine ⟨146707303012318881451477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 782438949399034034407877 146707303012318881451477)
          ·
            refine ⟨3438452414351223784019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 146707303012318881451477 3438452414351223784019)
            ·
              rfl

theorem cell20_203402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 7].length) (baseStart_203402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203402 prefixEnd_203402 := by exact prefixLift 203402
  have htrace : WordTrace (prefixWord ++ tailWord_203402) baseStart_203402 baseEnd_203402 := by
    simpa [prefixWord, tailWord_203402, baseEnd_203402] using wordTrace_append hprefix tailTrace_203402
  have hstable : (prefixWord ++ tailWord_203402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203402).length < 2 ^ (prefixWord ++ tailWord_203402).sum := by decide
  have hdescent : baseEnd_203402 < baseStart_203402 := by decide
  rcases family_descends (prefixWord ++ tailWord_203402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203416 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_203416 : Nat := 118140960795 + 203416 * 2 ^ 59
def prefixEnd_203416 : Nat := 4983230072969 + 3 ^ 40 * 203416 * 2
def baseEnd_203416 : Nat := 92844605168961215701789

theorem tailTrace_203416 : CollatzResearch.WordTrace tailWord_203416 prefixEnd_203416 92844605168961215701789 := by
  unfold tailWord_203416
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709595515533023766031051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4946127354044031688041401 3709595515533023766031051)
  ·
    refine ⟨5564393273299535649046577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3709595515533023766031051 5564393273299535649046577)
    ·
      refine ⟨4173294954974651736784933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5564393273299535649046577 4173294954974651736784933)
      ·
        refine ⟨782492804057747200647175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4173294954974651736784933 782492804057747200647175)
        ·
          refine ⟨1173739206086620800970763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782492804057747200647175 1173739206086620800970763)
          ·
            refine ⟨1760608809129931201456145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173739206086620800970763 1760608809129931201456145)
            ·
              refine ⟨1320456606847448401092109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760608809129931201456145 1320456606847448401092109)
              ·
                refine ⟨495171227567793150409541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1320456606847448401092109 495171227567793150409541)
                ·
                  refine ⟨92844605168961215701789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 495171227567793150409541 92844605168961215701789)
                  ·
                    rfl

theorem cell20_203416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_203416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203416 prefixEnd_203416 := by exact prefixLift 203416
  have htrace : WordTrace (prefixWord ++ tailWord_203416) baseStart_203416 baseEnd_203416 := by
    simpa [prefixWord, tailWord_203416, baseEnd_203416] using wordTrace_append hprefix tailTrace_203416
  have hstable : (prefixWord ++ tailWord_203416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203416).length < 2 ^ (prefixWord ++ tailWord_203416).sum := by decide
  have hdescent : baseEnd_203416 < baseStart_203416 := by decide
  rcases family_descends (prefixWord ++ tailWord_203416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203446 : List Nat := [5, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_203446 : Nat := 118140960795 + 203446 * 2 ^ 59
def prefixEnd_203446 : Nat := 4983230072969 + 3 ^ 40 * 203446 * 2
def baseEnd_203446 : Nat := 92858297986414444701667

theorem tailTrace_203446 : CollatzResearch.WordTrace tailWord_203446 prefixEnd_203446 92858297986414444701667 := by
  unfold tailWord_203446
  simp only [CollatzResearch.WordTrace]
  refine ⟨463767826309835165978387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4946856813971575103769461 463767826309835165978387)
  ·
    refine ⟨695651739464752748967581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 463767826309835165978387 695651739464752748967581)
    ·
      refine ⟨260869402299282280862843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 695651739464752748967581 260869402299282280862843)
      ·
        refine ⟨391304103448923421294265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260869402299282280862843 391304103448923421294265)
        ·
          refine ⟨293478077586692565970699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391304103448923421294265 293478077586692565970699)
          ·
            refine ⟨440217116380038848956049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293478077586692565970699 440217116380038848956049)
            ·
              refine ⟨330162837285029136717037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440217116380038848956049 330162837285029136717037)
              ·
                refine ⟨123811063981885926268889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330162837285029136717037 123811063981885926268889)
                ·
                  refine ⟨92858297986414444701667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123811063981885926268889 92858297986414444701667)
                  ·
                    rfl

theorem cell20_203446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_203446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203446 prefixEnd_203446 := by exact prefixLift 203446
  have htrace : WordTrace (prefixWord ++ tailWord_203446) baseStart_203446 baseEnd_203446 := by
    simpa [prefixWord, tailWord_203446, baseEnd_203446] using wordTrace_append hprefix tailTrace_203446
  have hstable : (prefixWord ++ tailWord_203446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203446).length < 2 ^ (prefixWord ++ tailWord_203446).sum := by decide
  have hdescent : baseEnd_203446 < baseStart_203446 := by decide
  rcases family_descends (prefixWord ++ tailWord_203446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203454 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_203454 : Nat := 118140960795 + 203454 * 2 ^ 59
def prefixEnd_203454 : Nat := 4983230072969 + 3 ^ 40 * 203454 * 2
def baseEnd_203454 : Nat := 92861949404401972434967

theorem tailTrace_203454 : CollatzResearch.WordTrace tailWord_203454 prefixEnd_203454 92861949404401972434967 := by
  unfold tailWord_203454
  simp only [CollatzResearch.WordTrace]
  refine ⟨927572125616047502743177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4947051336618920014630277 927572125616047502743177)
  ·
    refine ⟨695679094212035627057383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 927572125616047502743177 695679094212035627057383)
    ·
      refine ⟨1043518641318053440586075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695679094212035627057383 1043518641318053440586075)
      ·
        refine ⟨1565277961977080160879113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1043518641318053440586075 1565277961977080160879113)
        ·
          refine ⟨1173958471482810120659335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1565277961977080160879113 1173958471482810120659335)
          ·
            refine ⟨1760937707224215180989003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173958471482810120659335 1760937707224215180989003)
            ·
              refine ⟨2641406560836322771483505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760937707224215180989003 2641406560836322771483505)
              ·
                refine ⟨1981054920627242078612629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641406560836322771483505 1981054920627242078612629)
                ·
                  refine ⟨92861949404401972434967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1981054920627242078612629 92861949404401972434967)
                  ·
                    rfl

theorem cell20_203454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_203454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203454 prefixEnd_203454 := by exact prefixLift 203454
  have htrace : WordTrace (prefixWord ++ tailWord_203454) baseStart_203454 baseEnd_203454 := by
    simpa [prefixWord, tailWord_203454, baseEnd_203454] using wordTrace_append hprefix tailTrace_203454
  have hstable : (prefixWord ++ tailWord_203454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203454).length < 2 ^ (prefixWord ++ tailWord_203454).sum := by decide
  have hdescent : baseEnd_203454 < baseStart_203454 := by decide
  rcases family_descends (prefixWord ++ tailWord_203454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203457 : List Nat := [1, 2, 6, 2, 1, 1, 7]
def baseStart_203457 : Nat := 118140960795 + 203457 * 2 ^ 59
def prefixEnd_203457 : Nat := 4983230072969 + 3 ^ 40 * 203457 * 2
def baseEnd_203457 : Nat := 10318146520683032814995

theorem tailTrace_203457 : CollatzResearch.WordTrace tailWord_203457 prefixEnd_203457 10318146520683032814995 := by
  unfold tailWord_203457
  simp only [CollatzResearch.WordTrace]
  refine ⟨7420686423917511534304625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4947124282611674356203083 7420686423917511534304625)
  ·
    refine ⟨5565514817938133650728469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7420686423917511534304625 5565514817938133650728469)
    ·
      refine ⟨260883507090850014877897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5565514817938133650728469 260883507090850014877897)
      ·
        refine ⟨195662630318137511158423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260883507090850014877897 195662630318137511158423)
        ·
          refine ⟨293493945477206266737635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195662630318137511158423 293493945477206266737635)
          ·
            refine ⟨440240918215809400106453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293493945477206266737635 440240918215809400106453)
            ·
              refine ⟨10318146520683032814995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 440240918215809400106453 10318146520683032814995)
              ·
                rfl

theorem cell20_203457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 7].length) (baseStart_203457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203457 prefixEnd_203457 := by exact prefixLift 203457
  have htrace : WordTrace (prefixWord ++ tailWord_203457) baseStart_203457 baseEnd_203457 := by
    simpa [prefixWord, tailWord_203457, baseEnd_203457] using wordTrace_append hprefix tailTrace_203457
  have hstable : (prefixWord ++ tailWord_203457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203457).length < 2 ^ (prefixWord ++ tailWord_203457).sum := by decide
  have hdescent : baseEnd_203457 < baseStart_203457 := by decide
  rcases family_descends (prefixWord ++ tailWord_203457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203464 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 3]
def baseStart_203464 : Nat := 118140960795 + 203464 * 2 ^ 59
def prefixEnd_203464 : Nat := 4983230072969 + 3 ^ 40 * 203464 * 2
def baseEnd_203464 : Nat := 92866513676886382101593

theorem tailTrace_203464 : CollatzResearch.WordTrace tailWord_203464 prefixEnd_203464 92866513676886382101593 := by
  unfold tailWord_203464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3710470867446075864904723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4947294489928101153206297 3710470867446075864904723)
  ·
    refine ⟨5565706301169113797357085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3710470867446075864904723 5565706301169113797357085)
    ·
      refine ⟨2087139862938417674008907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5565706301169113797357085 2087139862938417674008907)
      ·
        refine ⟨3130709794407626511013361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087139862938417674008907 3130709794407626511013361)
        ·
          refine ⟨2348032345805719883260021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3130709794407626511013361 2348032345805719883260021)
          ·
            refine ⟨220128032419286239055627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2348032345805719883260021 220128032419286239055627)
            ·
              refine ⟨330192048628929358583441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220128032419286239055627 330192048628929358583441)
              ·
                refine ⟨247644036471697018937581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330192048628929358583441 247644036471697018937581)
                ·
                  refine ⟨92866513676886382101593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247644036471697018937581 92866513676886382101593)
                  ·
                    rfl

theorem cell20_203464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_203464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203464 prefixEnd_203464 := by exact prefixLift 203464
  have htrace : WordTrace (prefixWord ++ tailWord_203464) baseStart_203464 baseEnd_203464 := by
    simpa [prefixWord, tailWord_203464, baseEnd_203464] using wordTrace_append hprefix tailTrace_203464
  have hstable : (prefixWord ++ tailWord_203464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203464).length < 2 ^ (prefixWord ++ tailWord_203464).sum := by decide
  have hdescent : baseEnd_203464 < baseStart_203464 := by decide
  rcases family_descends (prefixWord ++ tailWord_203464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203492 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_203492 : Nat := 118140960795 + 203492 * 2 ^ 59
def prefixEnd_203492 : Nat := 4983230072969 + 3 ^ 40 * 203492 * 2
def baseEnd_203492 : Nat := 92879293639842729168145

theorem tailTrace_203492 : CollatzResearch.WordTrace tailWord_203492 prefixEnd_203492 92879293639842729168145 := by
  unfold tailWord_203492
  simp only [CollatzResearch.WordTrace]
  refine ⟨3710981489395356255914365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4947975319193808341219153 3710981489395356255914365)
  ·
    refine ⟨1391618058523258595967887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3710981489395356255914365 1391618058523258595967887)
    ·
      refine ⟨2087427087784887893951831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391618058523258595967887 2087427087784887893951831)
      ·
        refine ⟨3131140631677331840927747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087427087784887893951831 3131140631677331840927747)
        ·
          refine ⟨4696710947515997761391621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131140631677331840927747 4696710947515997761391621)
          ·
            refine ⟨880633302659249580260929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4696710947515997761391621 880633302659249580260929)
            ·
              refine ⟨660474976994437185195697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880633302659249580260929 660474976994437185195697)
              ·
                refine ⟨495356232745827888896773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660474976994437185195697 495356232745827888896773)
                ·
                  refine ⟨92879293639842729168145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 495356232745827888896773 92879293639842729168145)
                  ·
                    rfl

theorem cell20_203492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_203492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203492 prefixEnd_203492 := by exact prefixLift 203492
  have htrace : WordTrace (prefixWord ++ tailWord_203492) baseStart_203492 baseEnd_203492 := by
    simpa [prefixWord, tailWord_203492, baseEnd_203492] using wordTrace_append hprefix tailTrace_203492
  have hstable : (prefixWord ++ tailWord_203492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203492).length < 2 ^ (prefixWord ++ tailWord_203492).sum := by decide
  have hdescent : baseEnd_203492 < baseStart_203492 := by decide
  rcases family_descends (prefixWord ++ tailWord_203492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203513 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_203513 : Nat := 118140960795 + 203513 * 2 ^ 59
def prefixEnd_203513 : Nat := 4983230072969 + 3 ^ 40 * 203513 * 2
def baseEnd_203513 : Nat := 92888878612059989468059

theorem tailTrace_203513 : CollatzResearch.WordTrace tailWord_203513 prefixEnd_203513 92888878612059989468059 := by
  unfold tailWord_203513
  simp only [CollatzResearch.WordTrace]
  refine ⟨7422728911714633098343193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4948485941143088732228795 7422728911714633098343193)
  ·
    refine ⟨5567046683785974823757395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7422728911714633098343193 5567046683785974823757395)
    ·
      refine ⟨8350570025678962235636093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5567046683785974823757395 8350570025678962235636093)
      ·
        refine ⟨3131463759629610838363535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8350570025678962235636093 3131463759629610838363535)
        ·
          refine ⟨4697195639444416257545303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131463759629610838363535 4697195639444416257545303)
          ·
            refine ⟨7045793459166624386317955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697195639444416257545303 7045793459166624386317955)
            ·
              refine ⟨10568690188749936579476933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7045793459166624386317955 10568690188749936579476933)
              ·
                refine ⟨1981629410390613108651925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10568690188749936579476933 1981629410390613108651925)
                ·
                  refine ⟨92888878612059989468059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1981629410390613108651925 92888878612059989468059)
                  ·
                    rfl

theorem cell20_203513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_203513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203513 prefixEnd_203513 := by exact prefixLift 203513
  have htrace : WordTrace (prefixWord ++ tailWord_203513) baseStart_203513 baseEnd_203513 := by
    simpa [prefixWord, tailWord_203513, baseEnd_203513] using wordTrace_append hprefix tailTrace_203513
  have hstable : (prefixWord ++ tailWord_203513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203513).length < 2 ^ (prefixWord ++ tailWord_203513).sum := by decide
  have hdescent : baseEnd_203513 < baseStart_203513 := by decide
  rcases family_descends (prefixWord ++ tailWord_203513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203578 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_203578 : Nat := 118140960795 + 203578 * 2 ^ 59
def prefixEnd_203578 : Nat := 4983230072969 + 3 ^ 40 * 203578 * 2
def baseEnd_203578 : Nat := 92918546383208652301127

theorem tailTrace_203578 : CollatzResearch.WordTrace tailWord_203578 prefixEnd_203578 92918546383208652301127 := by
  unfold tailWord_203578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1856274914119787299864847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4950066437652766132972925 1856274914119787299864847)
  ·
    refine ⟨2784412371179680949797271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1856274914119787299864847 2784412371179680949797271)
    ·
      refine ⟨4176618556769521424695907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2784412371179680949797271 4176618556769521424695907)
      ·
        refine ⟨6264927835154282137043861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4176618556769521424695907 6264927835154282137043861)
        ·
          refine ⟨293668492272856975173931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6264927835154282137043861 293668492272856975173931)
          ·
            refine ⟨440502738409285462760897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293668492272856975173931 440502738409285462760897)
            ·
              refine ⟨330377053806964097070673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440502738409285462760897 330377053806964097070673)
              ·
                refine ⟨247782790355223072803005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330377053806964097070673 247782790355223072803005)
                ·
                  refine ⟨92918546383208652301127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247782790355223072803005 92918546383208652301127)
                  ·
                    rfl

theorem cell20_203578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_203578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203578 prefixEnd_203578 := by exact prefixLift 203578
  have htrace : WordTrace (prefixWord ++ tailWord_203578) baseStart_203578 baseEnd_203578 := by
    simpa [prefixWord, tailWord_203578, baseEnd_203578] using wordTrace_append hprefix tailTrace_203578
  have hstable : (prefixWord ++ tailWord_203578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203578).length < 2 ^ (prefixWord ++ tailWord_203578).sum := by decide
  have hdescent : baseEnd_203578 < baseStart_203578 := by decide
  rcases family_descends (prefixWord ++ tailWord_203578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203588 : List Nat := [2, 3, 4, 2, 1, 2, 1, 5]
def baseStart_203588 : Nat := 118140960795 + 203588 * 2 ^ 59
def prefixEnd_203588 : Nat := 4983230072969 + 3 ^ 40 * 203588 * 2
def baseEnd_203588 : Nat := 30974370218564353989251

theorem tailTrace_203588 : CollatzResearch.WordTrace tailWord_203588 prefixEnd_203588 30974370218564353989251 := by
  unfold tailWord_203588
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712732193221460453661709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4950309590961947271548945 3712732193221460453661709)
  ·
    refine ⟨1392274572458047670123141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3712732193221460453661709 1392274572458047670123141)
    ·
      refine ⟨261051482335883938148089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1392274572458047670123141 261051482335883938148089)
      ·
        refine ⟨195788611751912953611067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261051482335883938148089 195788611751912953611067)
        ·
          refine ⟨293682917627869430416601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195788611751912953611067 293682917627869430416601)
          ·
            refine ⟨220262188220902072812451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293682917627869430416601 220262188220902072812451)
            ·
              refine ⟨330393282331353109218677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220262188220902072812451 330393282331353109218677)
              ·
                refine ⟨30974370218564353989251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 330393282331353109218677 30974370218564353989251)
                ·
                  rfl

theorem cell20_203588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_203588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203588 prefixEnd_203588 := by exact prefixLift 203588
  have htrace : WordTrace (prefixWord ++ tailWord_203588) baseStart_203588 baseEnd_203588 := by
    simpa [prefixWord, tailWord_203588, baseEnd_203588] using wordTrace_append hprefix tailTrace_203588
  have hstable : (prefixWord ++ tailWord_203588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203588).length < 2 ^ (prefixWord ++ tailWord_203588).sum := by decide
  have hdescent : baseEnd_203588 < baseStart_203588 := by decide
  rcases family_descends (prefixWord ++ tailWord_203588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203623 : List Nat := [1, 1, 5, 1, 2, 2, 1, 5, 2]
def baseStart_203623 : Nat := 118140960795 + 203623 * 2 ^ 59
def prefixEnd_203623 : Nat := 4983230072969 + 3 ^ 40 * 203623 * 2
def baseEnd_203623 : Nat := 92939085609388495800943

theorem tailTrace_203623 : CollatzResearch.WordTrace tailWord_203623 prefixEnd_203623 92939085609388495800943 := by
  unfold tailWord_203623
  simp only [CollatzResearch.WordTrace]
  refine ⟨7426740941316121884847523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4951160627544081256565015 7426740941316121884847523)
  ·
    refine ⟨11140111411974182827271285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7426740941316121884847523 11140111411974182827271285)
    ·
      refine ⟨1044385444872579640056683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11140111411974182827271285 1044385444872579640056683)
      ·
        refine ⟨1566578167308869460085025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044385444872579640056683 1566578167308869460085025)
        ·
          refine ⟨1174933625481652095063769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566578167308869460085025 1174933625481652095063769)
          ·
            refine ⟨881200219111239071297827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174933625481652095063769 881200219111239071297827)
            ·
              refine ⟨1321800328666858606946741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881200219111239071297827 1321800328666858606946741)
              ·
                refine ⟨123918780812517994401257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1321800328666858606946741 123918780812517994401257)
                ·
                  refine ⟨92939085609388495800943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123918780812517994401257 92939085609388495800943)
                  ·
                    rfl

theorem cell20_203623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 2].length) (baseStart_203623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203623 prefixEnd_203623 := by exact prefixLift 203623
  have htrace : WordTrace (prefixWord ++ tailWord_203623) baseStart_203623 baseEnd_203623 := by
    simpa [prefixWord, tailWord_203623, baseEnd_203623] using wordTrace_append hprefix tailTrace_203623
  have hstable : (prefixWord ++ tailWord_203623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203623).length < 2 ^ (prefixWord ++ tailWord_203623).sum := by decide
  have hdescent : baseEnd_203623 < baseStart_203623 := by decide
  rcases family_descends (prefixWord ++ tailWord_203623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203630 : List Nat := [4, 1, 2, 3, 2, 1, 7]
def baseStart_203630 : Nat := 118140960795 + 203630 * 2 ^ 59
def prefixEnd_203630 : Nat := 4983230072969 + 3 ^ 40 * 203630 * 2
def baseEnd_203630 : Nat := 10326920066680842507509

theorem tailTrace_203630 : CollatzResearch.WordTrace tailWord_203630 prefixEnd_203630 10326920066680842507509 := by
  unfold tailWord_203630
  simp only [CollatzResearch.WordTrace]
  refine ⟨928374531536345260044043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4951330834860508053568229 928374531536345260044043)
  ·
    refine ⟨1392561797304517890066065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 928374531536345260044043 1392561797304517890066065)
    ·
      refine ⟨1044421347978388417549549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1392561797304517890066065 1044421347978388417549549)
      ·
        refine ⟨391658005491895656581081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1044421347978388417549549 391658005491895656581081)
        ·
          refine ⟨293743504118921742435811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391658005491895656581081 293743504118921742435811)
          ·
            refine ⟨440615256178382613653717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293743504118921742435811 440615256178382613653717)
            ·
              refine ⟨10326920066680842507509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 440615256178382613653717 10326920066680842507509)
              ·
                rfl

theorem cell20_203630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 7].length) (baseStart_203630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203630 prefixEnd_203630 := by exact prefixLift 203630
  have htrace : WordTrace (prefixWord ++ tailWord_203630) baseStart_203630 baseEnd_203630 := by
    simpa [prefixWord, tailWord_203630, baseEnd_203630] using wordTrace_append hprefix tailTrace_203630
  have hstable : (prefixWord ++ tailWord_203630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203630).length < 2 ^ (prefixWord ++ tailWord_203630).sum := by decide
  have hdescent : baseEnd_203630 < baseStart_203630 := by decide
  rcases family_descends (prefixWord ++ tailWord_203630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203637 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 5]
def baseStart_203637 : Nat := 118140960795 + 203637 * 2 ^ 59
def prefixEnd_203637 : Nat := 4983230072969 + 3 ^ 40 * 203637 * 2
def baseEnd_203637 : Nat := 92945475590866669334219

theorem tailTrace_203637 : CollatzResearch.WordTrace tailWord_203637 prefixEnd_203637 92945475590866669334219 := by
  unfold tailWord_203637
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427251563265402275857165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4951501042176934850571443 7427251563265402275857165)
  ·
    refine ⟨2785219336224525853446437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7427251563265402275857165 2785219336224525853446437)
    ·
      refine ⟨522228625542098597521207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2785219336224525853446437 522228625542098597521207)
      ·
        refine ⟨783342938313147896281811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522228625542098597521207 783342938313147896281811)
        ·
          refine ⟨1175014407469721844422717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783342938313147896281811 1175014407469721844422717)
          ·
            refine ⟨440630402801145691658519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1175014407469721844422717 440630402801145691658519)
            ·
              refine ⟨660945604201718537487779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440630402801145691658519 660945604201718537487779)
              ·
                refine ⟨991418406302577806231669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660945604201718537487779 991418406302577806231669)
                ·
                  refine ⟨92945475590866669334219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 991418406302577806231669 92945475590866669334219)
                  ·
                    rfl

theorem cell20_203637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_203637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203637 prefixEnd_203637 := by exact prefixLift 203637
  have htrace : WordTrace (prefixWord ++ tailWord_203637) baseStart_203637 baseEnd_203637 := by
    simpa [prefixWord, tailWord_203637, baseEnd_203637] using wordTrace_append hprefix tailTrace_203637
  have hstable : (prefixWord ++ tailWord_203637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203637).length < 2 ^ (prefixWord ++ tailWord_203637).sum := by decide
  have hdescent : baseEnd_203637 < baseStart_203637 := by decide
  rcases family_descends (prefixWord ++ tailWord_203637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203709 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 3]
def baseStart_203709 : Nat := 118140960795 + 203709 * 2 ^ 59
def prefixEnd_203709 : Nat := 4983230072969 + 3 ^ 40 * 203709 * 2
def baseEnd_203709 : Nat := 92978338352754418933925

theorem tailTrace_203709 : CollatzResearch.WordTrace tailWord_203709 prefixEnd_203709 92978338352754418933925 := by
  unfold tailWord_203709
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429877619004558572478181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4953251746003039048318787 7429877619004558572478181)
  ·
    refine ⟨1393102053563354732339659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7429877619004558572478181 1393102053563354732339659)
    ·
      refine ⟨2089653080345032098509489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393102053563354732339659 2089653080345032098509489)
      ·
        refine ⟨1567239810258774073882117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2089653080345032098509489 1567239810258774073882117)
        ·
          refine ⟨293857464423520138852897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1567239810258774073882117 293857464423520138852897)
          ·
            refine ⟨220393098317640104139673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293857464423520138852897 220393098317640104139673)
            ·
              refine ⟨165294823738230078104755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220393098317640104139673 165294823738230078104755)
              ·
                refine ⟨247942235607345117157133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165294823738230078104755 247942235607345117157133)
                ·
                  refine ⟨92978338352754418933925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247942235607345117157133 92978338352754418933925)
                  ·
                    rfl

theorem cell20_203709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_203709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203709 prefixEnd_203709 := by exact prefixLift 203709
  have htrace : WordTrace (prefixWord ++ tailWord_203709) baseStart_203709 baseEnd_203709 := by
    simpa [prefixWord, tailWord_203709, baseEnd_203709] using wordTrace_append hprefix tailTrace_203709
  have hstable : (prefixWord ++ tailWord_203709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203709).length < 2 ^ (prefixWord ++ tailWord_203709).sum := by decide
  have hdescent : baseEnd_203709 < baseStart_203709 := by decide
  rcases family_descends (prefixWord ++ tailWord_203709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203751 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 3]
def baseStart_203751 : Nat := 118140960795 + 203751 * 2 ^ 59
def prefixEnd_203751 : Nat := 4983230072969 + 3 ^ 40 * 203751 * 2
def baseEnd_203751 : Nat := 92997508297188939533753

theorem tailTrace_203751 : CollatzResearch.WordTrace tailWord_203751 prefixEnd_203751 92997508297188939533753 := by
  unfold tailWord_203751
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431409484852399745507107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4954272989901599830338071 7431409484852399745507107)
  ·
    refine ⟨11147114227278599618260661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7431409484852399745507107 11147114227278599618260661)
    ·
      refine ⟨1045041958807368714211937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11147114227278599618260661 1045041958807368714211937)
      ·
        refine ⟨783781469105526535658953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1045041958807368714211937 783781469105526535658953)
        ·
          refine ⟨587836101829144901744215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 783781469105526535658953 587836101829144901744215)
          ·
            refine ⟨881754152743717352616323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587836101829144901744215 881754152743717352616323)
            ·
              refine ⟨1322631229115576028924485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881754152743717352616323 1322631229115576028924485)
              ·
                refine ⟨247993355459170505423341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1322631229115576028924485 247993355459170505423341)
                ·
                  refine ⟨92997508297188939533753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247993355459170505423341 92997508297188939533753)
                  ·
                    rfl

theorem cell20_203751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 3].length) (baseStart_203751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203751 prefixEnd_203751 := by exact prefixLift 203751
  have htrace : WordTrace (prefixWord ++ tailWord_203751) baseStart_203751 baseEnd_203751 := by
    simpa [prefixWord, tailWord_203751, baseEnd_203751] using wordTrace_append hprefix tailTrace_203751
  have hstable : (prefixWord ++ tailWord_203751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203751).length < 2 ^ (prefixWord ++ tailWord_203751).sum := by decide
  have hdescent : baseEnd_203751 < baseStart_203751 := by decide
  rcases family_descends (prefixWord ++ tailWord_203751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203754 : List Nat := [3, 1, 3, 1, 2, 2, 4, 2, 2]
def baseStart_203754 : Nat := 118140960795 + 203754 * 2 ^ 59
def prefixEnd_203754 : Nat := 4983230072969 + 3 ^ 40 * 203754 * 2
def baseEnd_203754 : Nat := 92998877578934262433741

theorem tailTrace_203754 : CollatzResearch.WordTrace tailWord_203754 prefixEnd_203754 92998877578934262433741 := by
  unfold tailWord_203754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857879725960382814466579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4954345935894354171910877 1857879725960382814466579)
  ·
    refine ⟨2786819588940574221699869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1857879725960382814466579 2786819588940574221699869)
    ·
      refine ⟨1045057345852715333137451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2786819588940574221699869 1045057345852715333137451)
      ·
        refine ⟨1567586018779072999706177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045057345852715333137451 1567586018779072999706177)
        ·
          refine ⟨1175689514084304749779633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1567586018779072999706177 1175689514084304749779633)
          ·
            refine ⟨881767135563228562334725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1175689514084304749779633 881767135563228562334725)
            ·
              refine ⟨165331337918105355437761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 881767135563228562334725 165331337918105355437761)
              ·
                refine ⟨123998503438579016578321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165331337918105355437761 123998503438579016578321)
                ·
                  refine ⟨92998877578934262433741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123998503438579016578321 92998877578934262433741)
                  ·
                    rfl

theorem cell20_203754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_203754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203754 prefixEnd_203754 := by exact prefixLift 203754
  have htrace : WordTrace (prefixWord ++ tailWord_203754) baseStart_203754 baseEnd_203754 := by
    simpa [prefixWord, tailWord_203754, baseEnd_203754] using wordTrace_append hprefix tailTrace_203754
  have hstable : (prefixWord ++ tailWord_203754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203754).length < 2 ^ (prefixWord ++ tailWord_203754).sum := by decide
  have hdescent : baseEnd_203754 < baseStart_203754 := by decide
  rcases family_descends (prefixWord ++ tailWord_203754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203778 : List Nat := [3, 4, 1, 3, 1, 1, 3, 4]
def baseStart_203778 : Nat := 118140960795 + 203778 * 2 ^ 59
def prefixEnd_203778 : Nat := 4983230072969 + 3 ^ 40 * 203778 * 2
def baseEnd_203778 : Nat := 31003277277632281877881

theorem tailTrace_203778 : CollatzResearch.WordTrace tailWord_203778 prefixEnd_203778 31003277277632281877881 := by
  unfold tailWord_203778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858098563938645839184997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4954929503836388904493325 1858098563938645839184997)
  ·
    refine ⟨348393480738496094847187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1858098563938645839184997 348393480738496094847187)
    ·
      refine ⟨522590221107744142270781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348393480738496094847187 522590221107744142270781)
      ·
        refine ⟨195971332915404053351543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522590221107744142270781 195971332915404053351543)
        ·
          refine ⟨293956999373106080027315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195971332915404053351543 293956999373106080027315)
          ·
            refine ⟨440935499059659120040973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293956999373106080027315 440935499059659120040973)
            ·
              refine ⟨165350812147372170015365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 440935499059659120040973 165350812147372170015365)
              ·
                refine ⟨31003277277632281877881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165350812147372170015365 31003277277632281877881)
                ·
                  rfl

theorem cell20_203778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_203778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203778 prefixEnd_203778 := by exact prefixLift 203778
  have htrace : WordTrace (prefixWord ++ tailWord_203778) baseStart_203778 baseEnd_203778 := by
    simpa [prefixWord, tailWord_203778, baseEnd_203778] using wordTrace_append hprefix tailTrace_203778
  have hstable : (prefixWord ++ tailWord_203778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203778).length < 2 ^ (prefixWord ++ tailWord_203778).sum := by decide
  have hdescent : baseEnd_203778 < baseStart_203778 := by decide
  rcases family_descends (prefixWord ++ tailWord_203778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203824 : List Nat := [2, 1, 1, 1, 2, 4, 2, 7]
def baseStart_203824 : Nat := 118140960795 + 203824 * 2 ^ 59
def prefixEnd_203824 : Nat := 4983230072969 + 3 ^ 40 * 203824 * 2
def baseEnd_203824 : Nat := 31010275828775043366707

theorem tailTrace_203824 : CollatzResearch.WordTrace tailWord_203824 prefixEnd_203824 31010275828775043366707 := by
  unfold tailWord_203824
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717036006793966606457263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4956048009058622141943017 3717036006793966606457263)
  ·
    refine ⟨5575554010190949909685895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3717036006793966606457263 5575554010190949909685895)
    ·
      refine ⟨8363331015286424864528843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5575554010190949909685895 8363331015286424864528843)
      ·
        refine ⟨12544996522929637296793265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8363331015286424864528843 12544996522929637296793265)
        ·
          refine ⟨9408747392197227972594949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12544996522929637296793265 9408747392197227972594949)
          ·
            refine ⟨1764140136036980244861553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9408747392197227972594949 1764140136036980244861553)
            ·
              refine ⟨1323105102027735183646165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1764140136036980244861553 1323105102027735183646165)
              ·
                refine ⟨31010275828775043366707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1323105102027735183646165 31010275828775043366707)
                ·
                  rfl

theorem cell20_203824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_203824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203824 prefixEnd_203824 := by exact prefixLift 203824
  have htrace : WordTrace (prefixWord ++ tailWord_203824) baseStart_203824 baseEnd_203824 := by
    simpa [prefixWord, tailWord_203824, baseEnd_203824] using wordTrace_append hprefix tailTrace_203824
  have hstable : (prefixWord ++ tailWord_203824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203824).length < 2 ^ (prefixWord ++ tailWord_203824).sum := by decide
  have hdescent : baseEnd_203824 < baseStart_203824 := by decide
  rcases family_descends (prefixWord ++ tailWord_203824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203868 : List Nat := [2, 2, 4, 1, 1, 1, 5, 2, 2]
def baseStart_203868 : Nat := 118140960795 + 203868 * 2 ^ 59
def prefixEnd_203868 : Nat := 4983230072969 + 3 ^ 40 * 203868 * 2
def baseEnd_203868 : Nat := 93050910285256532633275

theorem tailTrace_203868 : CollatzResearch.WordTrace tailWord_203868 prefixEnd_203868 93050910285256532633275 := by
  unfold tailWord_203868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717838412714264363758129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4957117883619019151677505 3717838412714264363758129)
  ·
    refine ⟨2788378809535698272818597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3717838412714264363758129 2788378809535698272818597)
    ·
      refine ⟨522821026787943426153487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2788378809535698272818597 522821026787943426153487)
      ·
        refine ⟨784231540181915139230231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522821026787943426153487 784231540181915139230231)
        ·
          refine ⟨1176347310272872708845347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784231540181915139230231 1176347310272872708845347)
          ·
            refine ⟨1764520965409309063268021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176347310272872708845347 1764520965409309063268021)
            ·
              refine ⟨165423840507122724681377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1764520965409309063268021 165423840507122724681377)
              ·
                refine ⟨124067880380342043511033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165423840507122724681377 124067880380342043511033)
                ·
                  refine ⟨93050910285256532633275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124067880380342043511033 93050910285256532633275)
                  ·
                    rfl

theorem cell20_203868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_203868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203868 prefixEnd_203868 := by exact prefixLift 203868
  have htrace : WordTrace (prefixWord ++ tailWord_203868) baseStart_203868 baseEnd_203868 := by
    simpa [prefixWord, tailWord_203868, baseEnd_203868] using wordTrace_append hprefix tailTrace_203868
  have hstable : (prefixWord ++ tailWord_203868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203868).length < 2 ^ (prefixWord ++ tailWord_203868).sum := by decide
  have hdescent : baseEnd_203868 < baseStart_203868 := by decide
  rcases family_descends (prefixWord ++ tailWord_203868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203879 : List Nat := [1, 1, 5, 1, 1, 4, 2, 5]
def baseStart_203879 : Nat := 118140960795 + 203879 * 2 ^ 59
def prefixEnd_203879 : Nat := 4983230072969 + 3 ^ 40 * 203879 * 2
def baseEnd_203879 : Nat := 31018643661663127755521

theorem tailTrace_203879 : CollatzResearch.WordTrace tailWord_203879 prefixEnd_203879 31018643661663127755521 := by
  unfold tailWord_203879
  simp only [CollatzResearch.WordTrace]
  refine ⟨7436078028388677606166691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4957385352259118404111127 7436078028388677606166691)
  ·
    refine ⟨11154117042583016409250037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7436078028388677606166691 11154117042583016409250037)
    ·
      refine ⟨1045698472742157788367191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11154117042583016409250037 1045698472742157788367191)
      ·
        refine ⟨1568547709113236682550787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045698472742157788367191 1568547709113236682550787)
        ·
          refine ⟨2352821563669855023826181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568547709113236682550787 2352821563669855023826181)
          ·
            refine ⟨441154043188097816967409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2352821563669855023826181 441154043188097816967409)
            ·
              refine ⟨330865532391073362725557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441154043188097816967409 330865532391073362725557)
              ·
                refine ⟨31018643661663127755521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 330865532391073362725557 31018643661663127755521)
                ·
                  rfl

theorem cell20_203879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_203879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203879 prefixEnd_203879 := by exact prefixLift 203879
  have htrace : WordTrace (prefixWord ++ tailWord_203879) baseStart_203879 baseEnd_203879 := by
    simpa [prefixWord, tailWord_203879, baseEnd_203879] using wordTrace_append hprefix tailTrace_203879
  have hstable : (prefixWord ++ tailWord_203879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203879).length < 2 ^ (prefixWord ++ tailWord_203879).sum := by decide
  have hdescent : baseEnd_203879 < baseStart_203879 := by decide
  rcases family_descends (prefixWord ++ tailWord_203879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203882 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_203882 : Nat := 118140960795 + 203882 * 2 ^ 59
def prefixEnd_203882 : Nat := 4983230072969 + 3 ^ 40 * 203882 * 2
def baseEnd_203882 : Nat := 93057300266734706166551

theorem tailTrace_203882 : CollatzResearch.WordTrace tailWord_203882 prefixEnd_203882 93057300266734706166551 := by
  unfold tailWord_203882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859046861844452279631475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4957458298251872745683933 1859046861844452279631475)
  ·
    refine ⟨2788570292766678419447213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1859046861844452279631475 2788570292766678419447213)
    ·
      refine ⟨1045713859787504407292705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2788570292766678419447213 1045713859787504407292705)
      ·
        refine ⟨784285394840628305469529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1045713859787504407292705 784285394840628305469529)
        ·
          refine ⟨588214046130471229102147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784285394840628305469529 588214046130471229102147)
          ·
            refine ⟨882321069195706843653221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588214046130471229102147 882321069195706843653221)
            ·
              refine ⟨165435200474195033184979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 882321069195706843653221 165435200474195033184979)
              ·
                refine ⟨248152800711292549777469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165435200474195033184979 248152800711292549777469)
                ·
                  refine ⟨93057300266734706166551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248152800711292549777469 93057300266734706166551)
                  ·
                    rfl

theorem cell20_203882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_203882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203882 prefixEnd_203882 := by exact prefixLift 203882
  have htrace : WordTrace (prefixWord ++ tailWord_203882) baseStart_203882 baseEnd_203882 := by
    simpa [prefixWord, tailWord_203882, baseEnd_203882] using wordTrace_append hprefix tailTrace_203882
  have hstable : (prefixWord ++ tailWord_203882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203882).length < 2 ^ (prefixWord ++ tailWord_203882).sum := by decide
  have hdescent : baseEnd_203882 < baseStart_203882 := by decide
  rcases family_descends (prefixWord ++ tailWord_203882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203900 : List Nat := [2, 2, 2, 1, 1, 3, 1, 8]
def baseStart_203900 : Nat := 118140960795 + 203900 * 2 ^ 59
def prefixEnd_203900 : Nat := 4983230072969 + 3 ^ 40 * 203900 * 2
def baseEnd_203900 : Nat := 31021838652402214522159

theorem tailTrace_203900 : CollatzResearch.WordTrace tailWord_203900 prefixEnd_203900 31021838652402214522159 := by
  unfold tailWord_203900
  simp only [CollatzResearch.WordTrace]
  refine ⟨3718421980656299096340577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4957895974208398795120769 3718421980656299096340577)
  ·
    refine ⟨2788816485492224322255433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3718421980656299096340577 2788816485492224322255433)
    ·
      refine ⟨2091612364119168241691575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2788816485492224322255433 2091612364119168241691575)
      ·
        refine ⟨3137418546178752362537363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2091612364119168241691575 3137418546178752362537363)
        ·
          refine ⟨4706127819268128543806045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137418546178752362537363 4706127819268128543806045)
          ·
            refine ⟨1764797932225548203927267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4706127819268128543806045 1764797932225548203927267)
            ·
              refine ⟨2647196898338322305890901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764797932225548203927267 2647196898338322305890901)
              ·
                refine ⟨31021838652402214522159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2647196898338322305890901 31021838652402214522159)
                ·
                  rfl

theorem cell20_203900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_203900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203900 prefixEnd_203900 := by exact prefixLift 203900
  have htrace : WordTrace (prefixWord ++ tailWord_203900) baseStart_203900 baseEnd_203900 := by
    simpa [prefixWord, tailWord_203900, baseEnd_203900] using wordTrace_append hprefix tailTrace_203900
  have hstable : (prefixWord ++ tailWord_203900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203900).length < 2 ^ (prefixWord ++ tailWord_203900).sum := by decide
  have hdescent : baseEnd_203900 < baseStart_203900 := by decide
  rcases family_descends (prefixWord ++ tailWord_203900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203927 : List Nat := [1, 1, 3, 3, 3, 2, 1, 4, 2]
def baseStart_203927 : Nat := 118140960795 + 203927 * 2 ^ 59
def prefixEnd_203927 : Nat := 4983230072969 + 3 ^ 40 * 203927 * 2
def baseEnd_203927 : Nat := 93077839492914549666367

theorem tailTrace_203927 : CollatzResearch.WordTrace tailWord_203927 prefixEnd_203927 93077839492914549666367 := by
  unfold tailWord_203927
  simp only [CollatzResearch.WordTrace]
  refine ⟨7437828732214781803914035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4958552488143187869276023 7437828732214781803914035)
  ·
    refine ⟨11156743098322172705871053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7437828732214781803914035 11156743098322172705871053)
    ·
      refine ⟨4183778661870814764701645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11156743098322172705871053 4183778661870814764701645)
      ·
        refine ⟨1568916998201555536763117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4183778661870814764701645 1568916998201555536763117)
        ·
          refine ⟨588343874325583326286169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1568916998201555536763117 588343874325583326286169)
          ·
            refine ⟨441257905744187494714627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588343874325583326286169 441257905744187494714627)
            ·
              refine ⟨661886858616281242071941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441257905744187494714627 661886858616281242071941)
              ·
                refine ⟨124103785990552732888489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 661886858616281242071941 124103785990552732888489)
                ·
                  refine ⟨93077839492914549666367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124103785990552732888489 93077839492914549666367)
                  ·
                    rfl

theorem cell20_203927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 2].length) (baseStart_203927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203927 prefixEnd_203927 := by exact prefixLift 203927
  have htrace : WordTrace (prefixWord ++ tailWord_203927) baseStart_203927 baseEnd_203927 := by
    simpa [prefixWord, tailWord_203927, baseEnd_203927] using wordTrace_append hprefix tailTrace_203927
  have hstable : (prefixWord ++ tailWord_203927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203927).length < 2 ^ (prefixWord ++ tailWord_203927).sum := by decide
  have hdescent : baseEnd_203927 < baseStart_203927 := by decide
  rcases family_descends (prefixWord ++ tailWord_203927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203934 : List Nat := [4, 3, 1, 1, 2, 1, 3, 5]
def baseStart_203934 : Nat := 118140960795 + 203934 * 2 ^ 59
def prefixEnd_203934 : Nat := 4983230072969 + 3 ^ 40 * 203934 * 2
def baseEnd_203934 : Nat := 31027011494551212144335

theorem tailTrace_203934 : CollatzResearch.WordTrace tailWord_203934 prefixEnd_203934 31027011494551212144335 := by
  unfold tailWord_203934
  simp only [CollatzResearch.WordTrace]
  refine ⟨929760505398677749927357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4958722695459614666279237 929760505398677749927357)
  ·
    refine ⟨348660189524504156222759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 929760505398677749927357 348660189524504156222759)
    ·
      refine ⟨522990284286756234334139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348660189524504156222759 522990284286756234334139)
      ·
        refine ⟨784485426430134351501209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522990284286756234334139 784485426430134351501209)
        ·
          refine ⟨588364069822600763625907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784485426430134351501209 588364069822600763625907)
          ·
            refine ⟨882546104733901145438861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588364069822600763625907 882546104733901145438861)
            ·
              refine ⟨330954789275212929539573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 882546104733901145438861 330954789275212929539573)
              ·
                refine ⟨31027011494551212144335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 330954789275212929539573 31027011494551212144335)
                ·
                  rfl

theorem cell20_203934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_203934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203934 prefixEnd_203934 := by exact prefixLift 203934
  have htrace : WordTrace (prefixWord ++ tailWord_203934) baseStart_203934 baseEnd_203934 := by
    simpa [prefixWord, tailWord_203934, baseEnd_203934] using wordTrace_append hprefix tailTrace_203934
  have hstable : (prefixWord ++ tailWord_203934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203934).length < 2 ^ (prefixWord ++ tailWord_203934).sum := by decide
  have hdescent : baseEnd_203934 < baseStart_203934 := by decide
  rcases family_descends (prefixWord ++ tailWord_203934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203986 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_203986 : Nat := 118140960795 + 203986 * 2 ^ 59
def prefixEnd_203986 : Nat := 4983230072969 + 3 ^ 40 * 203986 * 2
def baseEnd_203986 : Nat := 93104768700572566699459

theorem tailTrace_203986 : CollatzResearch.WordTrace tailWord_203986 prefixEnd_203986 93104768700572566699459 := by
  unfold tailWord_203986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859995159750258720077953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4959987092667356586874541 1859995159750258720077953)
  ·
    refine ⟨1394996369812694040058465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1859995159750258720077953 1394996369812694040058465)
    ·
      refine ⟨1046247277359520530043849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1394996369812694040058465 1046247277359520530043849)
      ·
        refine ⟨784685458019640397532887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1046247277359520530043849 784685458019640397532887)
        ·
          refine ⟨1177028187029460596299331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784685458019640397532887 1177028187029460596299331)
          ·
            refine ⟨1765542280544190894448997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177028187029460596299331 1765542280544190894448997)
            ·
              refine ⟨331039177602035792709187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1765542280544190894448997 331039177602035792709187)
              ·
                refine ⟨496558766403053689063781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331039177602035792709187 496558766403053689063781)
                ·
                  refine ⟨93104768700572566699459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 496558766403053689063781 93104768700572566699459)
                  ·
                    rfl

theorem cell20_203986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_203986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_203986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_203986 prefixEnd_203986 := by exact prefixLift 203986
  have htrace : WordTrace (prefixWord ++ tailWord_203986) baseStart_203986 baseEnd_203986 := by
    simpa [prefixWord, tailWord_203986, baseEnd_203986] using wordTrace_append hprefix tailTrace_203986
  have hstable : (prefixWord ++ tailWord_203986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203986).length < 2 ^ (prefixWord ++ tailWord_203986).sum := by decide
  have hdescent : baseEnd_203986 < baseStart_203986 := by decide
  rcases family_descends (prefixWord ++ tailWord_203986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204010 : List Nat := [3, 1, 3, 1, 1, 5, 2, 4]
def baseStart_204010 : Nat := 118140960795 + 204010 * 2 ^ 59
def prefixEnd_204010 : Nat := 4983230072969 + 3 ^ 40 * 204010 * 2
def baseEnd_204010 : Nat := 31038574318178383299787

theorem tailTrace_204010 : CollatzResearch.WordTrace tailWord_204010 prefixEnd_204010 31038574318178383299787 := by
  unfold tailWord_204010
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860213997728521744796371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4960570660609391319456989 1860213997728521744796371)
  ·
    refine ⟨2790320996592782617194557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1860213997728521744796371 2790320996592782617194557)
    ·
      refine ⟨1046370373722293481447959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2790320996592782617194557 1046370373722293481447959)
      ·
        refine ⟨1569555560583440222171939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046370373722293481447959 1569555560583440222171939)
        ·
          refine ⟨2354333340875160333257909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569555560583440222171939 2354333340875160333257909)
          ·
            refine ⟨220718750707046281242929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2354333340875160333257909 220718750707046281242929)
            ·
              refine ⟨165539063030284710932197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220718750707046281242929 165539063030284710932197)
              ·
                refine ⟨31038574318178383299787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165539063030284710932197 31038574318178383299787)
                ·
                  rfl

theorem cell20_204010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_204010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204010 prefixEnd_204010 := by exact prefixLift 204010
  have htrace : WordTrace (prefixWord ++ tailWord_204010) baseStart_204010 baseEnd_204010 := by
    simpa [prefixWord, tailWord_204010, baseEnd_204010] using wordTrace_append hprefix tailTrace_204010
  have hstable : (prefixWord ++ tailWord_204010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204010).length < 2 ^ (prefixWord ++ tailWord_204010).sum := by decide
  have hdescent : baseEnd_204010 < baseStart_204010 := by decide
  rcases family_descends (prefixWord ++ tailWord_204010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204041 : List Nat := [1, 2, 1, 1, 3, 3, 5, 2, 2]
def baseStart_204041 : Nat := 118140960795 + 204041 * 2 ^ 59
def prefixEnd_204041 : Nat := 4983230072969 + 3 ^ 40 * 204041 * 2
def baseEnd_204041 : Nat := 93129872199236819865901

theorem tailTrace_204041 : CollatzResearch.WordTrace tailWord_204041 prefixEnd_204041 93129872199236819865901 := by
  unfold tailWord_204041
  simp only [CollatzResearch.WordTrace]
  refine ⟨7441986653801779273563977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4961324435867852849042651 7441986653801779273563977)
  ·
    refine ⟨5581489990351334455172983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7441986653801779273563977 5581489990351334455172983)
    ·
      refine ⟨8372234985527001682759475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5581489990351334455172983 8372234985527001682759475)
      ·
        refine ⟨12558352478290502524139213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8372234985527001682759475 12558352478290502524139213)
        ·
          refine ⟨4709382179358938446552205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12558352478290502524139213 4709382179358938446552205)
          ·
            refine ⟨1766018317259601917457077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4709382179358938446552205 1766018317259601917457077)
            ·
              refine ⟨165564217243087679761601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1766018317259601917457077 165564217243087679761601)
              ·
                refine ⟨124173162932315759821201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165564217243087679761601 124173162932315759821201)
                ·
                  refine ⟨93129872199236819865901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124173162932315759821201 93129872199236819865901)
                  ·
                    rfl

theorem cell20_204041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_204041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204041 prefixEnd_204041 := by exact prefixLift 204041
  have htrace : WordTrace (prefixWord ++ tailWord_204041) baseStart_204041 baseEnd_204041 := by
    simpa [prefixWord, tailWord_204041, baseEnd_204041] using wordTrace_append hprefix tailTrace_204041
  have hstable : (prefixWord ++ tailWord_204041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204041).length < 2 ^ (prefixWord ++ tailWord_204041).sum := by decide
  have hdescent : baseEnd_204041 < baseStart_204041 := by decide
  rcases family_descends (prefixWord ++ tailWord_204041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204086 : List Nat := [5, 1, 2, 3, 1, 8]
def baseStart_204086 : Nat := 118140960795 + 204086 * 2 ^ 59
def prefixEnd_204086 : Nat := 4983230072969 + 3 ^ 40 * 204086 * 2
def baseEnd_204086 : Nat := 3450015237978394939471

theorem tailTrace_204086 : CollatzResearch.WordTrace tailWord_204086 prefixEnd_204086 3450015237978394939471 := by
  unfold tailWord_204086
  simp only [CollatzResearch.WordTrace]
  refine ⟨465226746164921997434507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4962418625759167972634741 465226746164921997434507)
  ·
    refine ⟨697840119247382996151761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 465226746164921997434507 697840119247382996151761)
    ·
      refine ⟨523380089435537247113821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 697840119247382996151761 523380089435537247113821)
      ·
        refine ⟨196267533538326467667683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 523380089435537247113821 196267533538326467667683)
        ·
          refine ⟨294401300307489701501525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196267533538326467667683 294401300307489701501525)
          ·
            refine ⟨3450015237978394939471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 294401300307489701501525 3450015237978394939471)
            ·
              rfl

theorem cell20_204086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 8].length) (baseStart_204086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204086 prefixEnd_204086 := by exact prefixLift 204086
  have htrace : WordTrace (prefixWord ++ tailWord_204086) baseStart_204086 baseEnd_204086 := by
    simpa [prefixWord, tailWord_204086, baseEnd_204086] using wordTrace_append hprefix tailTrace_204086
  have hstable : (prefixWord ++ tailWord_204086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204086).length < 2 ^ (prefixWord ++ tailWord_204086).sum := by decide
  have hdescent : baseEnd_204086 < baseStart_204086 := by decide
  rcases family_descends (prefixWord ++ tailWord_204086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204200 : List Nat := [2, 1, 6, 1, 2, 2, 6]
def baseStart_204200 : Nat := 118140960795 + 204200 * 2 ^ 59
def prefixEnd_204200 : Nat := 4983230072969 + 3 ^ 40 * 204200 * 2
def baseEnd_204200 : Nat := 10355827125748770396139

theorem tailTrace_204200 : CollatzResearch.WordTrace tailWord_204200 prefixEnd_204200 10355827125748770396139 := by
  unfold tailWord_204200
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723892930112874714301027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4965190573483832952401369 3723892930112874714301027)
  ·
    refine ⟨5585839395169312071451541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3723892930112874714301027 5585839395169312071451541)
    ·
      refine ⟨261836221648561503349291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5585839395169312071451541 261836221648561503349291)
      ·
        refine ⟨392754332472842255023937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261836221648561503349291 392754332472842255023937)
        ·
          refine ⟨294565749354631691267953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392754332472842255023937 294565749354631691267953)
          ·
            refine ⟨220924312015973768450965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294565749354631691267953 220924312015973768450965)
            ·
              refine ⟨10355827125748770396139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220924312015973768450965 10355827125748770396139)
              ·
                rfl

theorem cell20_204200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 6].length) (baseStart_204200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204200 prefixEnd_204200 := by exact prefixLift 204200
  have htrace : WordTrace (prefixWord ++ tailWord_204200) baseStart_204200 baseEnd_204200 := by
    simpa [prefixWord, tailWord_204200, baseEnd_204200] using wordTrace_append hprefix tailTrace_204200
  have hstable : (prefixWord ++ tailWord_204200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204200).length < 2 ^ (prefixWord ++ tailWord_204200).sum := by decide
  have hdescent : baseEnd_204200 < baseStart_204200 := by decide
  rcases family_descends (prefixWord ++ tailWord_204200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204256 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_204256 : Nat := 118140960795 + 204256 * 2 ^ 59
def prefixEnd_204256 : Nat := 4983230072969 + 3 ^ 40 * 204256 * 2
def baseEnd_204256 : Nat := 93228004057651627698355

theorem tailTrace_204256 : CollatzResearch.WordTrace tailWord_204256 prefixEnd_204256 93228004057651627698355 := by
  unfold tailWord_204256
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724914174011435496320311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4966552232015247328427081 3724914174011435496320311)
  ·
    refine ⟨5587371261017153244480467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3724914174011435496320311 5587371261017153244480467)
    ·
      refine ⟨8381056891525729866720701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5587371261017153244480467 8381056891525729866720701)
      ·
        refine ⟨3142896334322148700020263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8381056891525729866720701 3142896334322148700020263)
        ·
          refine ⟨4714344501483223050030395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3142896334322148700020263 4714344501483223050030395)
          ·
            refine ⟨7071516752224834575045593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4714344501483223050030395 7071516752224834575045593)
            ·
              refine ⟨5303637564168625931284195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7071516752224834575045593 5303637564168625931284195)
              ·
                refine ⟨7955456346252938896926293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303637564168625931284195 7955456346252938896926293)
                ·
                  refine ⟨93228004057651627698355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7955456346252938896926293 93228004057651627698355)
                  ·
                    rfl

theorem cell20_204256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_204256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204256 prefixEnd_204256 := by exact prefixLift 204256
  have htrace : WordTrace (prefixWord ++ tailWord_204256) baseStart_204256 baseEnd_204256 := by
    simpa [prefixWord, tailWord_204256, baseEnd_204256] using wordTrace_append hprefix tailTrace_204256
  have hstable : (prefixWord ++ tailWord_204256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204256).length < 2 ^ (prefixWord ++ tailWord_204256).sum := by decide
  have hdescent : baseEnd_204256 < baseStart_204256 := by decide
  rcases family_descends (prefixWord ++ tailWord_204256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204280 : List Nat := [2, 1, 2, 1, 1, 5, 3, 5]
def baseStart_204280 : Nat := 118140960795 + 204280 * 2 ^ 59
def prefixEnd_204280 : Nat := 4983230072969 + 3 ^ 40 * 204280 * 2
def baseEnd_204280 : Nat := 31079652770538070299419

theorem tailTrace_204280 : CollatzResearch.WordTrace tailWord_204280 prefixEnd_204280 31079652770538070299419 := by
  unfold tailWord_204280
  simp only [CollatzResearch.WordTrace]
  refine ⟨3725351849967961545757147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4967135799957282061009529 3725351849967961545757147)
  ·
    refine ⟨5588027774951942318635721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3725351849967961545757147 5588027774951942318635721)
    ·
      refine ⟨4191020831213956738976791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5588027774951942318635721 4191020831213956738976791)
      ·
        refine ⟨6286531246820935108465187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191020831213956738976791 6286531246820935108465187)
        ·
          refine ⟨9429796870231402662697781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6286531246820935108465187 9429796870231402662697781)
          ·
            refine ⟨884043456584193999627917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9429796870231402662697781 884043456584193999627917)
            ·
              refine ⟨331516296219072749860469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884043456584193999627917 331516296219072749860469)
              ·
                refine ⟨31079652770538070299419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 331516296219072749860469 31079652770538070299419)
                ·
                  rfl

theorem cell20_204280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_204280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204280 prefixEnd_204280 := by exact prefixLift 204280
  have htrace : WordTrace (prefixWord ++ tailWord_204280) baseStart_204280 baseEnd_204280 := by
    simpa [prefixWord, tailWord_204280, baseEnd_204280] using wordTrace_append hprefix tailTrace_204280
  have hstable : (prefixWord ++ tailWord_204280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204280).length < 2 ^ (prefixWord ++ tailWord_204280).sum := by decide
  have hdescent : baseEnd_204280 < baseStart_204280 := by decide
  rcases family_descends (prefixWord ++ tailWord_204280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204290 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_204290 : Nat := 118140960795 + 204290 * 2 ^ 59
def prefixEnd_204290 : Nat := 4983230072969 + 3 ^ 40 * 204290 * 2
def baseEnd_204290 : Nat := 93243522584098620564883

theorem tailTrace_204290 : CollatzResearch.WordTrace tailWord_204290 prefixEnd_204290 93243522584098620564883 := by
  unfold tailWord_204290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1862767107474923699844581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4967378953266463199585549 1862767107474923699844581)
  ·
    refine ⟨349268832651548193720859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1862767107474923699844581 349268832651548193720859)
    ·
      refine ⟨523903248977322290581289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349268832651548193720859 523903248977322290581289)
      ·
        refine ⟨392927436732991717935967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523903248977322290581289 392927436732991717935967)
        ·
          refine ⟨589391155099487576903951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392927436732991717935967 589391155099487576903951)
          ·
            refine ⟨884086732649231365355927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589391155099487576903951 884086732649231365355927)
            ·
              refine ⟨1326130098973847048033891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884086732649231365355927 1326130098973847048033891)
              ·
                refine ⟨1989195148460770572050837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326130098973847048033891 1989195148460770572050837)
                ·
                  refine ⟨93243522584098620564883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1989195148460770572050837 93243522584098620564883)
                  ·
                    rfl

theorem cell20_204290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_204290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204290 prefixEnd_204290 := by exact prefixLift 204290
  have htrace : WordTrace (prefixWord ++ tailWord_204290) baseStart_204290 baseEnd_204290 := by
    simpa [prefixWord, tailWord_204290, baseEnd_204290] using wordTrace_append hprefix tailTrace_204290
  have hstable : (prefixWord ++ tailWord_204290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204290).length < 2 ^ (prefixWord ++ tailWord_204290).sum := by decide
  have hdescent : baseEnd_204290 < baseStart_204290 := by decide
  rcases family_descends (prefixWord ++ tailWord_204290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204321 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 3]
def baseStart_204321 : Nat := 118140960795 + 204321 * 2 ^ 59
def prefixEnd_204321 : Nat := 4983230072969 + 3 ^ 40 * 204321 * 2
def baseEnd_204321 : Nat := 93257671828800290531423

theorem tailTrace_204321 : CollatzResearch.WordTrace tailWord_204321 prefixEnd_204321 93257671828800290531423 := by
  unfold tailWord_204321
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452199092787387093756817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4968132728524924729171211 7452199092787387093756817)
  ·
    refine ⟨5589149319590540320317613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7452199092787387093756817 5589149319590540320317613)
    ·
      refine ⟨2095930994846452620119105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5589149319590540320317613 2095930994846452620119105)
      ·
        refine ⟨1571948246134839465089329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2095930994846452620119105 1571948246134839465089329)
        ·
          refine ⟨1178961184601129598816997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1571948246134839465089329 1178961184601129598816997)
          ·
            refine ⟨221055222112711799778187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1178961184601129598816997 221055222112711799778187)
            ·
              refine ⟨331582833169067699667281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221055222112711799778187 331582833169067699667281)
              ·
                refine ⟨248687124876800774750461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331582833169067699667281 248687124876800774750461)
                ·
                  refine ⟨93257671828800290531423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248687124876800774750461 93257671828800290531423)
                  ·
                    rfl

theorem cell20_204321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_204321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204321 prefixEnd_204321 := by exact prefixLift 204321
  have htrace : WordTrace (prefixWord ++ tailWord_204321) baseStart_204321 baseEnd_204321 := by
    simpa [prefixWord, tailWord_204321, baseEnd_204321] using wordTrace_append hprefix tailTrace_204321
  have hstable : (prefixWord ++ tailWord_204321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204321).length < 2 ^ (prefixWord ++ tailWord_204321).sum := by decide
  have hdescent : baseEnd_204321 < baseStart_204321 := by decide
  rcases family_descends (prefixWord ++ tailWord_204321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204358 : List Nat := [6, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_204358 : Nat := 118140960795 + 204358 * 2 ^ 59
def prefixEnd_204358 : Nat := 4983230072969 + 3 ^ 40 * 204358 * 2
def baseEnd_204358 : Nat := 93274559636992606297939

theorem tailTrace_204358 : CollatzResearch.WordTrace tailWord_204358 prefixEnd_204358 93274559636992606297939 := by
  unfold tailWord_204358
  simp only [CollatzResearch.WordTrace]
  refine ⟨232923393551666950401679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4969032395768894941902485 232923393551666950401679)
  ·
    refine ⟨349385090327500425602519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232923393551666950401679 349385090327500425602519)
    ·
      refine ⟨524077635491250638403779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349385090327500425602519 524077635491250638403779)
      ·
        refine ⟨786116453236875957605669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524077635491250638403779 786116453236875957605669)
        ·
          refine ⟨147396834981914242051063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 786116453236875957605669 147396834981914242051063)
          ·
            refine ⟨221095252472871363076595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147396834981914242051063 221095252472871363076595)
            ·
              refine ⟨331642878709307044614893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221095252472871363076595 331642878709307044614893)
              ·
                refine ⟨124366079515990141730585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331642878709307044614893 124366079515990141730585)
                ·
                  refine ⟨93274559636992606297939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124366079515990141730585 93274559636992606297939)
                  ·
                    rfl

theorem cell20_204358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_204358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204358 prefixEnd_204358 := by exact prefixLift 204358
  have htrace : WordTrace (prefixWord ++ tailWord_204358) baseStart_204358 baseEnd_204358 := by
    simpa [prefixWord, tailWord_204358, baseEnd_204358] using wordTrace_append hprefix tailTrace_204358
  have hstable : (prefixWord ++ tailWord_204358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204358).length < 2 ^ (prefixWord ++ tailWord_204358).sum := by decide
  have hdescent : baseEnd_204358 < baseStart_204358 := by decide
  rcases family_descends (prefixWord ++ tailWord_204358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204380 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_204380 : Nat := 118140960795 + 204380 * 2 ^ 59
def prefixEnd_204380 : Nat := 4983230072969 + 3 ^ 40 * 204380 * 2
def baseEnd_204380 : Nat := 93284601036458307564515

theorem tailTrace_204380 : CollatzResearch.WordTrace tailWord_204380 prefixEnd_204380 93284601036458307564515 := by
  unfold tailWord_204380
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727175499786820085077297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4969567333049093446769729 3727175499786820085077297)
  ·
    refine ⟨2795381624840115063807973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3727175499786820085077297 2795381624840115063807973)
    ·
      refine ⟨524134054657521574463995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2795381624840115063807973 524134054657521574463995)
      ·
        refine ⟨786201081986282361695993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524134054657521574463995 786201081986282361695993)
        ·
          refine ⟨589650811489711771271995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786201081986282361695993 589650811489711771271995)
          ·
            refine ⟨884476217234567656907993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589650811489711771271995 884476217234567656907993)
            ·
              refine ⟨663357162925925742680995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884476217234567656907993 663357162925925742680995)
              ·
                refine ⟨995035744388888614021493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663357162925925742680995 995035744388888614021493)
                ·
                  refine ⟨93284601036458307564515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 995035744388888614021493 93284601036458307564515)
                  ·
                    rfl

theorem cell20_204380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_204380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204380 prefixEnd_204380 := by exact prefixLift 204380
  have htrace : WordTrace (prefixWord ++ tailWord_204380) baseStart_204380 baseEnd_204380 := by
    simpa [prefixWord, tailWord_204380, baseEnd_204380] using wordTrace_append hprefix tailTrace_204380
  have hstable : (prefixWord ++ tailWord_204380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204380).length < 2 ^ (prefixWord ++ tailWord_204380).sum := by decide
  have hdescent : baseEnd_204380 < baseStart_204380 := by decide
  rcases family_descends (prefixWord ++ tailWord_204380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204387 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 4]
def baseStart_204387 : Nat := 118140960795 + 204387 * 2 ^ 59
def prefixEnd_204387 : Nat := 4983230072969 + 3 ^ 40 * 204387 * 2
def baseEnd_204387 : Nat := 93287796027197394331153

theorem tailTrace_204387 : CollatzResearch.WordTrace tailWord_204387 prefixEnd_204387 93287796027197394331153 := by
  unfold tailWord_204387
  simp only [CollatzResearch.WordTrace]
  refine ⟨7454606310548280365659415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4969737540365520243772943 7454606310548280365659415)
  ·
    refine ⟨11181909465822420548489123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7454606310548280365659415 11181909465822420548489123)
    ·
      refine ⟨16772864198733630822733685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11181909465822420548489123 16772864198733630822733685)
      ·
        refine ⟨1572456018631277889631283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16772864198733630822733685 1572456018631277889631283)
        ·
          refine ⟨2358684027946916834446925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572456018631277889631283 2358684027946916834446925)
          ·
            refine ⟨884506510480093812917597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2358684027946916834446925 884506510480093812917597)
            ·
              refine ⟨331689941430035179844099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884506510480093812917597 331689941430035179844099)
              ·
                refine ⟨497534912145052769766149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331689941430035179844099 497534912145052769766149)
                ·
                  refine ⟨93287796027197394331153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 497534912145052769766149 93287796027197394331153)
                  ·
                    rfl

theorem cell20_204387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_204387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204387 prefixEnd_204387 := by exact prefixLift 204387
  have htrace : WordTrace (prefixWord ++ tailWord_204387) baseStart_204387 baseEnd_204387 := by
    simpa [prefixWord, tailWord_204387, baseEnd_204387] using wordTrace_append hprefix tailTrace_204387
  have hstable : (prefixWord ++ tailWord_204387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204387).length < 2 ^ (prefixWord ++ tailWord_204387).sum := by decide
  have hdescent : baseEnd_204387 < baseStart_204387 := by decide
  rcases family_descends (prefixWord ++ tailWord_204387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204394 : List Nat := [3, 1, 3, 2, 1, 2, 1, 7]
def baseStart_204394 : Nat := 118140960795 + 204394 * 2 ^ 59
def prefixEnd_204394 : Nat := 4983230072969 + 3 ^ 40 * 204394 * 2
def baseEnd_204394 : Nat := 31096997005978827032597

theorem tailTrace_204394 : CollatzResearch.WordTrace tailWord_204394 prefixEnd_204394 31096997005978827032597 := by
  unfold tailWord_204394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863715405380730140291059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4969907747681947040776157 1863715405380730140291059)
  ·
    refine ⟨2795573108071095210436589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1863715405380730140291059 2795573108071095210436589)
    ·
      refine ⟨1048339915526660703913721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2795573108071095210436589 1048339915526660703913721)
      ·
        refine ⟨786254936644995527935291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1048339915526660703913721 786254936644995527935291)
        ·
          refine ⟨1179382404967493291902937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786254936644995527935291 1179382404967493291902937)
          ·
            refine ⟨884536803725619968927203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1179382404967493291902937 884536803725619968927203)
            ·
              refine ⟨1326805205588429953390805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884536803725619968927203 1326805205588429953390805)
              ·
                refine ⟨31096997005978827032597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1326805205588429953390805 31096997005978827032597)
                ·
                  rfl

theorem cell20_204394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_204394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204394 prefixEnd_204394 := by exact prefixLift 204394
  have htrace : WordTrace (prefixWord ++ tailWord_204394) baseStart_204394 baseEnd_204394 := by
    simpa [prefixWord, tailWord_204394, baseEnd_204394] using wordTrace_append hprefix tailTrace_204394
  have hstable : (prefixWord ++ tailWord_204394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204394).length < 2 ^ (prefixWord ++ tailWord_204394).sum := by decide
  have hdescent : baseEnd_204394 < baseStart_204394 := by decide
  rcases family_descends (prefixWord ++ tailWord_204394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204397 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 3]
def baseStart_204397 : Nat := 118140960795 + 204397 * 2 ^ 59
def prefixEnd_204397 : Nat := 4983230072969 + 3 ^ 40 * 204397 * 2
def baseEnd_204397 : Nat := 93292360299681803997779

theorem tailTrace_204397 : CollatzResearch.WordTrace tailWord_204397 prefixEnd_204397 93292360299681803997779 := by
  unfold tailWord_204397
  simp only [CollatzResearch.WordTrace]
  refine ⟨7454971040512052073523445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4969980693674701382348963 7454971040512052073523445)
  ·
    refine ⟨698903535048004881892823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7454971040512052073523445 698903535048004881892823)
    ·
      refine ⟨1048355302572007322839235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 698903535048004881892823 1048355302572007322839235)
      ·
        refine ⟨1572532953858010984258853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048355302572007322839235 1572532953858010984258853)
        ·
          refine ⟨294849928848377059548535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1572532953858010984258853 294849928848377059548535)
          ·
            refine ⟨442274893272565589322803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294849928848377059548535 442274893272565589322803)
            ·
              refine ⟨663412339908848383984205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442274893272565589322803 663412339908848383984205)
              ·
                refine ⟨248779627465818143994077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663412339908848383984205 248779627465818143994077)
                ·
                  refine ⟨93292360299681803997779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248779627465818143994077 93292360299681803997779)
                  ·
                    rfl

theorem cell20_204397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_204397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204397 prefixEnd_204397 := by exact prefixLift 204397
  have htrace : WordTrace (prefixWord ++ tailWord_204397) baseStart_204397 baseEnd_204397 := by
    simpa [prefixWord, tailWord_204397, baseEnd_204397] using wordTrace_append hprefix tailTrace_204397
  have hstable : (prefixWord ++ tailWord_204397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204397).length < 2 ^ (prefixWord ++ tailWord_204397).sum := by decide
  have hdescent : baseEnd_204397 < baseStart_204397 := by decide
  rcases family_descends (prefixWord ++ tailWord_204397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204449 : List Nat := [1, 2, 3, 3, 2, 3, 1, 5]
def baseStart_204449 : Nat := 118140960795 + 204449 * 2 ^ 59
def prefixEnd_204449 : Nat := 4983230072969 + 3 ^ 40 * 204449 * 2
def baseEnd_204449 : Nat := 31105364838866911421411

theorem tailTrace_204449 : CollatzResearch.WordTrace tailWord_204449 prefixEnd_204449 31105364838866911421411 := by
  unfold tailWord_204449
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456867636323664954416401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4971245090882443302944267 7456867636323664954416401)
  ·
    refine ⟨5592650727242748715812301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7456867636323664954416401 5592650727242748715812301)
    ·
      refine ⟨2097244022716030768429613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5592650727242748715812301 2097244022716030768429613)
      ·
        refine ⟨786466508518511538161105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2097244022716030768429613 786466508518511538161105)
        ·
          refine ⟨589849881388883653620829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786466508518511538161105 589849881388883653620829)
          ·
            refine ⟨221193705520831370107811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 589849881388883653620829 221193705520831370107811)
            ·
              refine ⟨331790558281247055161717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221193705520831370107811 331790558281247055161717)
              ·
                refine ⟨31105364838866911421411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 331790558281247055161717 31105364838866911421411)
                ·
                  rfl

theorem cell20_204449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 5].length) (baseStart_204449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204449 prefixEnd_204449 := by exact prefixLift 204449
  have htrace : WordTrace (prefixWord ++ tailWord_204449) baseStart_204449 baseEnd_204449 := by
    simpa [prefixWord, tailWord_204449, baseEnd_204449] using wordTrace_append hprefix tailTrace_204449
  have hstable : (prefixWord ++ tailWord_204449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204449).length < 2 ^ (prefixWord ++ tailWord_204449).sum := by decide
  have hdescent : baseEnd_204449 < baseStart_204449 := by decide
  rcases family_descends (prefixWord ++ tailWord_204449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204477 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_204477 : Nat := 118140960795 + 204477 * 2 ^ 59
def prefixEnd_204477 : Nat := 4983230072969 + 3 ^ 40 * 204477 * 2
def baseEnd_204477 : Nat := 93328874479557081330785

theorem tailTrace_204477 : CollatzResearch.WordTrace tailWord_204477 prefixEnd_204477 93328874479557081330785 := by
  unfold tailWord_204477
  simp only [CollatzResearch.WordTrace]
  refine ⟨7457888880222225736435685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4971925920148150490957123 7457888880222225736435685)
  ·
    refine ⟨1398354165041667325581691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7457888880222225736435685 1398354165041667325581691)
    ·
      refine ⟨2097531247562500988372537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398354165041667325581691 2097531247562500988372537)
      ·
        refine ⟨1573148435671875741279403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2097531247562500988372537 1573148435671875741279403)
        ·
          refine ⟨2359722653507813611919105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573148435671875741279403 2359722653507813611919105)
          ·
            refine ⟨1769791990130860208939329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2359722653507813611919105 1769791990130860208939329)
            ·
              refine ⟨1327343992598145156704497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1769791990130860208939329 1327343992598145156704497)
              ·
                refine ⟨995507994448608867528373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327343992598145156704497 995507994448608867528373)
                ·
                  refine ⟨93328874479557081330785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 995507994448608867528373 93328874479557081330785)
                  ·
                    rfl

theorem cell20_204477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_204477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204477 prefixEnd_204477 := by exact prefixLift 204477
  have htrace : WordTrace (prefixWord ++ tailWord_204477) baseStart_204477 baseEnd_204477 := by
    simpa [prefixWord, tailWord_204477, baseEnd_204477] using wordTrace_append hprefix tailTrace_204477
  have hstable : (prefixWord ++ tailWord_204477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204477).length < 2 ^ (prefixWord ++ tailWord_204477).sum := by decide
  have hdescent : baseEnd_204477 < baseStart_204477 := by decide
  rcases family_descends (prefixWord ++ tailWord_204477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204480 : List Nat := [2, 1, 1, 2, 4, 1, 4, 3, 2]
def baseStart_204480 : Nat := 118140960795 + 204480 * 2 ^ 59
def prefixEnd_204480 : Nat := 4983230072969 + 3 ^ 40 * 204480 * 2
def baseEnd_204480 : Nat := 93330243761302404230773

theorem tailTrace_204480 : CollatzResearch.WordTrace tailWord_204480 prefixEnd_204480 93330243761302404230773 := by
  unfold tailWord_204480
  simp only [CollatzResearch.WordTrace]
  refine ⟨3728999149605678624397447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4971998866140904832529929 3728999149605678624397447)
  ·
    refine ⟨5593498724408517936596171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3728999149605678624397447 5593498724408517936596171)
    ·
      refine ⟨8390248086612776904894257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5593498724408517936596171 8390248086612776904894257)
      ·
        refine ⟨6292686064959582678670693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8390248086612776904894257 6292686064959582678670693)
        ·
          refine ⟨1179878637179921752250755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6292686064959582678670693 1179878637179921752250755)
          ·
            refine ⟨1769817955769882628376133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179878637179921752250755 1769817955769882628376133)
            ·
              refine ⟨331840866706852992820525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1769817955769882628376133 331840866706852992820525)
              ·
                refine ⟨124440325015069872307697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331840866706852992820525 124440325015069872307697)
                ·
                  refine ⟨93330243761302404230773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124440325015069872307697 93330243761302404230773)
                  ·
                    rfl

theorem cell20_204480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_204480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204480 prefixEnd_204480 := by exact prefixLift 204480
  have htrace : WordTrace (prefixWord ++ tailWord_204480) baseStart_204480 baseEnd_204480 := by
    simpa [prefixWord, tailWord_204480, baseEnd_204480] using wordTrace_append hprefix tailTrace_204480
  have hstable : (prefixWord ++ tailWord_204480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204480).length < 2 ^ (prefixWord ++ tailWord_204480).sum := by decide
  have hdescent : baseEnd_204480 < baseStart_204480 := by decide
  rcases family_descends (prefixWord ++ tailWord_204480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204490 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 3]
def baseStart_204490 : Nat := 118140960795 + 204490 * 2 ^ 59
def prefixEnd_204490 : Nat := 4983230072969 + 3 ^ 40 * 204490 * 2
def baseEnd_204490 : Nat := 93334808033786813897399

theorem tailTrace_204490 : CollatzResearch.WordTrace tailWord_204490 prefixEnd_204490 93334808033786813897399 := by
  unfold tailWord_204490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864590757293782239164731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4972242019450085971105949 1864590757293782239164731)
  ·
    refine ⟨2796886135940673358747097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1864590757293782239164731 2796886135940673358747097)
    ·
      refine ⟨2097664601955505019060323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2796886135940673358747097 2097664601955505019060323)
      ·
        refine ⟨3146496902933257528590485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097664601955505019060323 3146496902933257528590485)
        ·
          refine ⟨147492042324996446652679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3146496902933257528590485 147492042324996446652679)
          ·
            refine ⟨221238063487494669979019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147492042324996446652679 221238063487494669979019)
            ·
              refine ⟨331857095231242004968529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221238063487494669979019 331857095231242004968529)
              ·
                refine ⟨248892821423431503726397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331857095231242004968529 248892821423431503726397)
                ·
                  refine ⟨93334808033786813897399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248892821423431503726397 93334808033786813897399)
                  ·
                    rfl

theorem cell20_204490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_204490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204490 prefixEnd_204490 := by exact prefixLift 204490
  have htrace : WordTrace (prefixWord ++ tailWord_204490) baseStart_204490 baseEnd_204490 := by
    simpa [prefixWord, tailWord_204490, baseEnd_204490] using wordTrace_append hprefix tailTrace_204490
  have hstable : (prefixWord ++ tailWord_204490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204490).length < 2 ^ (prefixWord ++ tailWord_204490).sum := by decide
  have hdescent : baseEnd_204490 < baseStart_204490 := by decide
  rcases family_descends (prefixWord ++ tailWord_204490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204525 : List Nat := [1, 5, 1, 2, 1, 2, 4, 4]
def baseStart_204525 : Nat := 118140960795 + 204525 * 2 ^ 59
def prefixEnd_204525 : Nat := 4983230072969 + 3 ^ 40 * 204525 * 2
def baseEnd_204525 : Nat := 31116927662494082576863

theorem tailTrace_204525 : CollatzResearch.WordTrace tailWord_204525 prefixEnd_204525 31116927662494082576863 := by
  unfold tailWord_204525
  simp only [CollatzResearch.WordTrace]
  refine ⟨7459639584048329934183029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4973093056032219956122019 7459639584048329934183029)
  ·
    refine ⟨699341211004530931329659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7459639584048329934183029 699341211004530931329659)
    ·
      refine ⟨1049011816506796396994489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 699341211004530931329659 1049011816506796396994489)
      ·
        refine ⟨786758862380097297745867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1049011816506796396994489 786758862380097297745867)
        ·
          refine ⟨1180138293570145946618801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786758862380097297745867 1180138293570145946618801)
          ·
            refine ⟨885103720177609459964101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1180138293570145946618801 885103720177609459964101)
            ·
              refine ⟨165956947533301773743269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 885103720177609459964101 165956947533301773743269)
              ·
                refine ⟨31116927662494082576863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165956947533301773743269 31116927662494082576863)
                ·
                  rfl

theorem cell20_204525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 4].length) (baseStart_204525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204525 prefixEnd_204525 := by exact prefixLift 204525
  have htrace : WordTrace (prefixWord ++ tailWord_204525) baseStart_204525 baseEnd_204525 := by
    simpa [prefixWord, tailWord_204525, baseEnd_204525] using wordTrace_append hprefix tailTrace_204525
  have hstable : (prefixWord ++ tailWord_204525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204525).length < 2 ^ (prefixWord ++ tailWord_204525).sum := by decide
  have hdescent : baseEnd_204525 < baseStart_204525 := by decide
  rcases family_descends (prefixWord ++ tailWord_204525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204539 : List Nat := [1, 1, 1, 1, 1, 3, 1, 9, 2]
def baseStart_204539 : Nat := 118140960795 + 204539 * 2 ^ 59
def prefixEnd_204539 : Nat := 4983230072969 + 3 ^ 40 * 204539 * 2
def baseEnd_204539 : Nat := 93357172968960421263865

theorem tailTrace_204539 : CollatzResearch.WordTrace tailWord_204539 prefixEnd_204539 93357172968960421263865 := by
  unfold tailWord_204539
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460150205997610325192671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4973433470665073550128447 7460150205997610325192671)
  ·
    refine ⟨11190225308996415487789007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7460150205997610325192671 11190225308996415487789007)
    ·
      refine ⟨16785337963494623231683511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11190225308996415487789007 16785337963494623231683511)
      ·
        refine ⟨25178006945241934847525267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16785337963494623231683511 25178006945241934847525267)
        ·
          refine ⟨37767010417862902271287901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25178006945241934847525267 37767010417862902271287901)
          ·
            refine ⟨14162628906698588351732963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37767010417862902271287901 14162628906698588351732963)
            ·
              refine ⟨21243943360047882527599445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14162628906698588351732963 21243943360047882527599445)
              ·
                refine ⟨124476230625280561685153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21243943360047882527599445 124476230625280561685153)
                ·
                  refine ⟨93357172968960421263865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124476230625280561685153 93357172968960421263865)
                  ·
                    rfl

theorem cell20_204539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 2].length) (baseStart_204539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204539 prefixEnd_204539 := by exact prefixLift 204539
  have htrace : WordTrace (prefixWord ++ tailWord_204539) baseStart_204539 baseEnd_204539 := by
    simpa [prefixWord, tailWord_204539, baseEnd_204539] using wordTrace_append hprefix tailTrace_204539
  have hstable : (prefixWord ++ tailWord_204539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204539).length < 2 ^ (prefixWord ++ tailWord_204539).sum := by decide
  have hdescent : baseEnd_204539 < baseStart_204539 := by decide
  rcases family_descends (prefixWord ++ tailWord_204539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204542 : List Nat := [4, 2, 2, 1, 4, 1, 6]
def baseStart_204542 : Nat := 118140960795 + 204542 * 2 ^ 59
def prefixEnd_204542 : Nat := 4983230072969 + 3 ^ 40 * 204542 * 2
def baseEnd_204542 : Nat := 10373171361189527129317

theorem tailTrace_204542 : CollatzResearch.WordTrace tailWord_204542 prefixEnd_204542 10373171361189527129317 := by
  unfold tailWord_204542
  simp only [CollatzResearch.WordTrace]
  refine ⟨932532453123342729693985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4973506416657827891701253 932532453123342729693985)
  ·
    refine ⟨699399339842507047270489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 932532453123342729693985 699399339842507047270489)
    ·
      refine ⟨524549504881880285452867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 699399339842507047270489 524549504881880285452867)
      ·
        refine ⟨786824257322820428179301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524549504881880285452867 786824257322820428179301)
        ·
          refine ⟨147529548248028830283619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 786824257322820428179301 147529548248028830283619)
          ·
            refine ⟨221294322372043245425429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147529548248028830283619 221294322372043245425429)
            ·
              refine ⟨10373171361189527129317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221294322372043245425429 10373171361189527129317)
              ·
                rfl

theorem cell20_204542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 6].length) (baseStart_204542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204542 prefixEnd_204542 := by exact prefixLift 204542
  have htrace : WordTrace (prefixWord ++ tailWord_204542) baseStart_204542 baseEnd_204542 := by
    simpa [prefixWord, tailWord_204542, baseEnd_204542] using wordTrace_append hprefix tailTrace_204542
  have hstable : (prefixWord ++ tailWord_204542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204542).length < 2 ^ (prefixWord ++ tailWord_204542).sum := by decide
  have hdescent : baseEnd_204542 < baseStart_204542 := by decide
  rcases family_descends (prefixWord ++ tailWord_204542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204553 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 3]
def baseStart_204553 : Nat := 118140960795 + 204553 * 2 ^ 59
def prefixEnd_204553 : Nat := 4983230072969 + 3 ^ 40 * 204553 * 2
def baseEnd_204553 : Nat := 93363562950438594797141

theorem tailTrace_204553 : CollatzResearch.WordTrace tailWord_204553 prefixEnd_204553 93363562950438594797141 := by
  unfold tailWord_204553
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460660827946890716202313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4973773885297927144134875 7460660827946890716202313)
  ·
    refine ⟨5595495620960168037151735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7460660827946890716202313 5595495620960168037151735)
    ·
      refine ⟨8393243431440252055727603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5595495620960168037151735 8393243431440252055727603)
      ·
        refine ⟨12589865147160378083591405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8393243431440252055727603 12589865147160378083591405)
        ·
          refine ⟨4721199430185141781346777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12589865147160378083591405 4721199430185141781346777)
          ·
            refine ⟨3540899572638856336010083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4721199430185141781346777 3540899572638856336010083)
            ·
              refine ⟨5311349358958284504015125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540899572638856336010083 5311349358958284504015125)
              ·
                refine ⟨248969501201169586125709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5311349358958284504015125 248969501201169586125709)
                ·
                  refine ⟨93363562950438594797141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248969501201169586125709 93363562950438594797141)
                  ·
                    rfl

theorem cell20_204553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_204553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204553 prefixEnd_204553 := by exact prefixLift 204553
  have htrace : WordTrace (prefixWord ++ tailWord_204553) baseStart_204553 baseEnd_204553 := by
    simpa [prefixWord, tailWord_204553, baseEnd_204553] using wordTrace_append hprefix tailTrace_204553
  have hstable : (prefixWord ++ tailWord_204553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204553).length < 2 ^ (prefixWord ++ tailWord_204553).sum := by decide
  have hdescent : baseEnd_204553 < baseStart_204553 := by decide
  rcases family_descends (prefixWord ++ tailWord_204553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204570 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_204570 : Nat := 118140960795 + 204570 * 2 ^ 59
def prefixEnd_204570 : Nat := 4983230072969 + 3 ^ 40 * 204570 * 2
def baseEnd_204570 : Nat := 93371322213662091230405

theorem tailTrace_204570 : CollatzResearch.WordTrace tailWord_204570 prefixEnd_204570 93371322213662091230405 := by
  unfold tailWord_204570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865320217221325654892791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4974187245923535079714109 1865320217221325654892791)
  ·
    refine ⟨2797980325831988482339187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1865320217221325654892791 2797980325831988482339187)
    ·
      refine ⟨4196970488747982723508781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2797980325831988482339187 4196970488747982723508781)
      ·
        refine ⟨1573863933280493521315793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4196970488747982723508781 1573863933280493521315793)
        ·
          refine ⟨1180397949960370140986845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573863933280493521315793 1180397949960370140986845)
          ·
            refine ⟨442649231235138802870067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1180397949960370140986845 442649231235138802870067)
            ·
              refine ⟨663973846852708204305101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442649231235138802870067 663973846852708204305101)
              ·
                refine ⟨248990192569765576614413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663973846852708204305101 248990192569765576614413)
                ·
                  refine ⟨93371322213662091230405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248990192569765576614413 93371322213662091230405)
                  ·
                    rfl

theorem cell20_204570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_204570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204570 prefixEnd_204570 := by exact prefixLift 204570
  have htrace : WordTrace (prefixWord ++ tailWord_204570) baseStart_204570 baseEnd_204570 := by
    simpa [prefixWord, tailWord_204570, baseEnd_204570] using wordTrace_append hprefix tailTrace_204570
  have hstable : (prefixWord ++ tailWord_204570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204570).length < 2 ^ (prefixWord ++ tailWord_204570).sum := by decide
  have hdescent : baseEnd_204570 < baseStart_204570 := by decide
  rcases family_descends (prefixWord ++ tailWord_204570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204584 : List Nat := [2, 1, 5, 1, 1, 2, 2, 6]
def baseStart_204584 : Nat := 118140960795 + 204584 * 2 ^ 59
def prefixEnd_204584 : Nat := 4983230072969 + 3 ^ 40 * 204584 * 2
def baseEnd_204584 : Nat := 31125904065046754921227

theorem tailTrace_204584 : CollatzResearch.WordTrace tailWord_204584 prefixEnd_204584 31125904065046754921227 := by
  unfold tailWord_204584
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730895745417291505290403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4974527660556388673720537 3730895745417291505290403)
  ·
    refine ⟨5596343618125937257935605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3730895745417291505290403 5596343618125937257935605)
    ·
      refine ⟨524657214199306617931463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5596343618125937257935605 524657214199306617931463)
      ·
        refine ⟨786985821298959926897195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524657214199306617931463 786985821298959926897195)
        ·
          refine ⟨1180478731948439890345793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786985821298959926897195 1180478731948439890345793)
          ·
            refine ⟨885359048961329917759345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1180478731948439890345793 885359048961329917759345)
            ·
              refine ⟨664019286720997438319509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885359048961329917759345 664019286720997438319509)
              ·
                refine ⟨31125904065046754921227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 664019286720997438319509 31125904065046754921227)
                ·
                  rfl

theorem cell20_204584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_204584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204584 prefixEnd_204584 := by exact prefixLift 204584
  have htrace : WordTrace (prefixWord ++ tailWord_204584) baseStart_204584 baseEnd_204584 := by
    simpa [prefixWord, tailWord_204584, baseEnd_204584] using wordTrace_append hprefix tailTrace_204584
  have hstable : (prefixWord ++ tailWord_204584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204584).length < 2 ^ (prefixWord ++ tailWord_204584).sum := by decide
  have hdescent : baseEnd_204584 < baseStart_204584 := by decide
  rcases family_descends (prefixWord ++ tailWord_204584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204601 : List Nat := [1, 2, 1, 7, 2, 7]
def baseStart_204601 : Nat := 118140960795 + 204601 * 2 ^ 59
def prefixEnd_204601 : Nat := 4983230072969 + 3 ^ 40 * 204601 * 2
def baseEnd_204601 : Nat := 3458721165124583748035

theorem tailTrace_204601 : CollatzResearch.WordTrace tailWord_204601 prefixEnd_204601 3458721165124583748035 := by
  unfold tailWord_204601
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462411531772994913949657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4974941021181996609299771 7462411531772994913949657)
  ·
    refine ⟨5596808648829746185462243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7462411531772994913949657 5596808648829746185462243)
    ·
      refine ⟨8395212973244619278193365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5596808648829746185462243 8395212973244619278193365)
      ·
        refine ⟨196762804060420764332657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8395212973244619278193365 196762804060420764332657)
        ·
          refine ⟨147572103045315573249493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196762804060420764332657 147572103045315573249493)
          ·
            refine ⟨3458721165124583748035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 147572103045315573249493 3458721165124583748035)
            ·
              rfl

theorem cell20_204601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 7].length) (baseStart_204601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204601 prefixEnd_204601 := by exact prefixLift 204601
  have htrace : WordTrace (prefixWord ++ tailWord_204601) baseStart_204601 baseEnd_204601 := by
    simpa [prefixWord, tailWord_204601, baseEnd_204601] using wordTrace_append hprefix tailTrace_204601
  have hstable : (prefixWord ++ tailWord_204601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204601).length < 2 ^ (prefixWord ++ tailWord_204601).sum := by decide
  have hdescent : baseEnd_204601 < baseStart_204601 := by decide
  rcases family_descends (prefixWord ++ tailWord_204601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204611 : List Nat := [1, 1, 1, 3, 1, 7, 2, 2, 2]
def baseStart_204611 : Nat := 118140960795 + 204611 * 2 ^ 59
def prefixEnd_204611 : Nat := 4983230072969 + 3 ^ 40 * 204611 * 2
def baseEnd_204611 : Nat := 93390035730848170863571

theorem tailTrace_204611 : CollatzResearch.WordTrace tailWord_204611 prefixEnd_204611 93390035730848170863571 := by
  unfold tailWord_204611
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462776261736766621813687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4975184174491177747875791 7462776261736766621813687)
  ·
    refine ⟨11194164392605149932720531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7462776261736766621813687 11194164392605149932720531)
    ·
      refine ⟨16791246588907724899080797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11194164392605149932720531 16791246588907724899080797)
      ·
        refine ⟨6296717470840396837155299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16791246588907724899080797 6296717470840396837155299)
        ·
          refine ⟨9445076206260595255732949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296717470840396837155299 9445076206260595255732949)
          ·
            refine ⟨221368973584232701306241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9445076206260595255732949 221368973584232701306241)
            ·
              refine ⟨166026730188174525979681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221368973584232701306241 166026730188174525979681)
              ·
                refine ⟨124520047641130894484761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166026730188174525979681 124520047641130894484761)
                ·
                  refine ⟨93390035730848170863571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124520047641130894484761 93390035730848170863571)
                  ·
                    rfl

theorem cell20_204611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 2].length) (baseStart_204611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204611 prefixEnd_204611 := by exact prefixLift 204611
  have htrace : WordTrace (prefixWord ++ tailWord_204611) baseStart_204611 baseEnd_204611 := by
    simpa [prefixWord, tailWord_204611, baseEnd_204611] using wordTrace_append hprefix tailTrace_204611
  have hstable : (prefixWord ++ tailWord_204611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204611).length < 2 ^ (prefixWord ++ tailWord_204611).sum := by decide
  have hdescent : baseEnd_204611 < baseStart_204611 := by decide
  rcases family_descends (prefixWord ++ tailWord_204611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204670 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_204670 : Nat := 118140960795 + 204670 * 2 ^ 59
def prefixEnd_204670 : Nat := 4983230072969 + 3 ^ 40 * 204670 * 2
def baseEnd_204670 : Nat := 93416964938506187896663

theorem tailTrace_204670 : CollatzResearch.WordTrace tailWord_204670 prefixEnd_204670 93416964938506187896663 := by
  unfold tailWord_204670
  simp only [CollatzResearch.WordTrace]
  refine ⟨933116021065377462276433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4976618779015346465474309 933116021065377462276433)
  ·
    refine ⟨699837015799033096707325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 933116021065377462276433 699837015799033096707325)
    ·
      refine ⟨262438880924637411265247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 699837015799033096707325 262438880924637411265247)
      ·
        refine ⟨393658321386956116897871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262438880924637411265247 393658321386956116897871)
        ·
          refine ⟨590487482080434175346807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393658321386956116897871 590487482080434175346807)
          ·
            refine ⟨885731223120651263020211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590487482080434175346807 885731223120651263020211)
            ·
              refine ⟨1328596834680976894530317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885731223120651263020211 1328596834680976894530317)
              ·
                refine ⟨498223813005366335448869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1328596834680976894530317 498223813005366335448869)
                ·
                  refine ⟨93416964938506187896663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498223813005366335448869 93416964938506187896663)
                  ·
                    rfl

theorem cell20_204670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_204670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204670 prefixEnd_204670 := by exact prefixLift 204670
  have htrace : WordTrace (prefixWord ++ tailWord_204670) baseStart_204670 baseEnd_204670 := by
    simpa [prefixWord, tailWord_204670, baseEnd_204670] using wordTrace_append hprefix tailTrace_204670
  have hstable : (prefixWord ++ tailWord_204670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204670).length < 2 ^ (prefixWord ++ tailWord_204670).sum := by decide
  have hdescent : baseEnd_204670 < baseStart_204670 := by decide
  rcases family_descends (prefixWord ++ tailWord_204670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204681 : List Nat := [1, 2, 1, 1, 5, 1, 2, 7]
def baseStart_204681 : Nat := 118140960795 + 204681 * 2 ^ 59
def prefixEnd_204681 : Nat := 4983230072969 + 3 ^ 40 * 204681 * 2
def baseEnd_204681 : Nat := 31140661879413012843317

theorem tailTrace_204681 : CollatzResearch.WordTrace tailWord_204681 prefixEnd_204681 31140661879413012843317 := by
  unfold tailWord_204681
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465329371483168576861897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4976886247655445717907931 7465329371483168576861897)
  ·
    refine ⟨5598997028612376432646423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7465329371483168576861897 5598997028612376432646423)
    ·
      refine ⟨8398495542918564648969635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5598997028612376432646423 8398495542918564648969635)
      ·
        refine ⟨12597743314377846973454453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8398495542918564648969635 12597743314377846973454453)
        ·
          refine ⟨1181038435722923153761355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12597743314377846973454453 1181038435722923153761355)
          ·
            refine ⟨1771557653584384730642033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181038435722923153761355 1771557653584384730642033)
            ·
              refine ⟨1328668240188288547981525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1771557653584384730642033 1328668240188288547981525)
              ·
                refine ⟨31140661879413012843317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1328668240188288547981525 31140661879413012843317)
                ·
                  rfl

theorem cell20_204681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_204681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204681 prefixEnd_204681 := by exact prefixLift 204681
  have htrace : WordTrace (prefixWord ++ tailWord_204681) baseStart_204681 baseEnd_204681 := by
    simpa [prefixWord, tailWord_204681, baseEnd_204681] using wordTrace_append hprefix tailTrace_204681
  have hstable : (prefixWord ++ tailWord_204681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204681).length < 2 ^ (prefixWord ++ tailWord_204681).sum := by decide
  have hdescent : baseEnd_204681 < baseStart_204681 := by decide
  rcases family_descends (prefixWord ++ tailWord_204681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204688 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_204688 : Nat := 118140960795 + 204688 * 2 ^ 59
def prefixEnd_204688 : Nat := 4983230072969 + 3 ^ 40 * 204688 * 2
def baseEnd_204688 : Nat := 93425180628978125296589

theorem tailTrace_204688 : CollatzResearch.WordTrace tailWord_204688 prefixEnd_204688 93425180628978125296589 := by
  unfold tailWord_204688
  simp only [CollatzResearch.WordTrace]
  refine ⟨3732792341228904386183359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4977056454971872514911145 3732792341228904386183359)
  ·
    refine ⟨5599188511843356579275039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3732792341228904386183359 5599188511843356579275039)
    ·
      refine ⟨8398782767765034868912559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5599188511843356579275039 8398782767765034868912559)
      ·
        refine ⟨12598174151647552303368839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8398782767765034868912559 12598174151647552303368839)
        ·
          refine ⟨18897261227471328455053259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12598174151647552303368839 18897261227471328455053259)
          ·
            refine ⟨28345891841206992682579889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18897261227471328455053259 28345891841206992682579889)
            ·
              refine ⟨21259418880905244511934917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28345891841206992682579889 21259418880905244511934917)
              ·
                refine ⟨3986141040169733345987797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21259418880905244511934917 3986141040169733345987797)
                ·
                  refine ⟨93425180628978125296589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3986141040169733345987797 93425180628978125296589)
                  ·
                    rfl

theorem cell20_204688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_204688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204688 prefixEnd_204688 := by exact prefixLift 204688
  have htrace : WordTrace (prefixWord ++ tailWord_204688) baseStart_204688 baseEnd_204688 := by
    simpa [prefixWord, tailWord_204688, baseEnd_204688] using wordTrace_append hprefix tailTrace_204688
  have hstable : (prefixWord ++ tailWord_204688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204688).length < 2 ^ (prefixWord ++ tailWord_204688).sum := by decide
  have hdescent : baseEnd_204688 < baseStart_204688 := by decide
  rcases family_descends (prefixWord ++ tailWord_204688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204698 : List Nat := [3, 1, 1, 4, 2, 2, 1, 6]
def baseStart_204698 : Nat := 118140960795 + 204698 * 2 ^ 59
def prefixEnd_204698 : Nat := 4983230072969 + 3 ^ 40 * 204698 * 2
def baseEnd_204698 : Nat := 31143248300487511654405

theorem tailTrace_204698 : CollatzResearch.WordTrace tailWord_204698 prefixEnd_204698 31143248300487511654405 := by
  unfold tailWord_204698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866487353105395120057687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4977299608281053653487165 1866487353105395120057687)
  ·
    refine ⟨2799731029658092680086531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1866487353105395120057687 2799731029658092680086531)
    ·
      refine ⟨4199596544487139020129797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2799731029658092680086531 4199596544487139020129797)
      ·
        refine ⟨787424352091338566274337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4199596544487139020129797 787424352091338566274337)
        ·
          refine ⟨590568264068503924705753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787424352091338566274337 590568264068503924705753)
          ·
            refine ⟨442926198051377943529315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590568264068503924705753 442926198051377943529315)
            ·
              refine ⟨664389297077066915293973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442926198051377943529315 664389297077066915293973)
              ·
                refine ⟨31143248300487511654405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 664389297077066915293973 31143248300487511654405)
                ·
                  rfl

theorem cell20_204698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_204698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204698 prefixEnd_204698 := by exact prefixLift 204698
  have htrace : WordTrace (prefixWord ++ tailWord_204698) baseStart_204698 baseEnd_204698 := by
    simpa [prefixWord, tailWord_204698, baseEnd_204698] using wordTrace_append hprefix tailTrace_204698
  have hstable : (prefixWord ++ tailWord_204698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204698).length < 2 ^ (prefixWord ++ tailWord_204698).sum := by decide
  have hdescent : baseEnd_204698 < baseStart_204698 := by decide
  rcases family_descends (prefixWord ++ tailWord_204698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204708 : List Nat := [2, 3, 1, 2, 1, 3, 3, 3, 2]
def baseStart_204708 : Nat := 118140960795 + 204708 * 2 ^ 59
def prefixEnd_204708 : Nat := 4983230072969 + 3 ^ 40 * 204708 * 2
def baseEnd_204708 : Nat := 93434309173946944629841

theorem tailTrace_204708 : CollatzResearch.WordTrace tailWord_204708 prefixEnd_204708 93434309173946944629841 := by
  unfold tailWord_204708
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733157071192676094047389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4977542761590234792063185 3733157071192676094047389)
  ·
    refine ⟨1399933901697253535267771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3733157071192676094047389 1399933901697253535267771)
    ·
      refine ⟨2099900852545880302901657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399933901697253535267771 2099900852545880302901657)
      ·
        refine ⟨1574925639409410227176243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2099900852545880302901657 1574925639409410227176243)
        ·
          refine ⟨2362388459114115340764365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574925639409410227176243 2362388459114115340764365)
          ·
            refine ⟨885895672167793252786637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2362388459114115340764365 885895672167793252786637)
            ·
              refine ⟨332210877062922469794989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 885895672167793252786637 332210877062922469794989)
              ·
                refine ⟨124579078898595926173121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332210877062922469794989 124579078898595926173121)
                ·
                  refine ⟨93434309173946944629841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124579078898595926173121 93434309173946944629841)
                  ·
                    rfl

theorem cell20_204708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_204708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204708 prefixEnd_204708 := by exact prefixLift 204708
  have htrace : WordTrace (prefixWord ++ tailWord_204708) baseStart_204708 baseEnd_204708 := by
    simpa [prefixWord, tailWord_204708, baseEnd_204708] using wordTrace_append hprefix tailTrace_204708
  have hstable : (prefixWord ++ tailWord_204708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204708).length < 2 ^ (prefixWord ++ tailWord_204708).sum := by decide
  have hdescent : baseEnd_204708 < baseStart_204708 := by decide
  rcases family_descends (prefixWord ++ tailWord_204708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204725 : List Nat := [1, 3, 3, 2, 1, 3, 3, 2, 2]
def baseStart_204725 : Nat := 118140960795 + 204725 * 2 ^ 59
def prefixEnd_204725 : Nat := 4983230072969 + 3 ^ 40 * 204725 * 2
def baseEnd_204725 : Nat := 93442068437170441063105

theorem tailTrace_204725 : CollatzResearch.WordTrace tailWord_204725 prefixEnd_204725 93442068437170441063105 := by
  unfold tailWord_204725
  simp only [CollatzResearch.WordTrace]
  refine ⟨7466934183323764091463629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4977956122215842727642419 7466934183323764091463629)
  ·
    refine ⟨2800100318746411534298861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7466934183323764091463629 2800100318746411534298861)
    ·
      refine ⟨1050037619529904325362073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2800100318746411534298861 1050037619529904325362073)
      ·
        refine ⟨787528214647428244021555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1050037619529904325362073 787528214647428244021555)
        ·
          refine ⟨1181292321971142366032333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787528214647428244021555 1181292321971142366032333)
          ·
            refine ⟨442984620739178387262125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1181292321971142366032333 442984620739178387262125)
            ·
              refine ⟨166119232777191895223297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 442984620739178387262125 166119232777191895223297)
              ·
                refine ⟨124589424582893921417473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166119232777191895223297 124589424582893921417473)
                ·
                  refine ⟨93442068437170441063105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124589424582893921417473 93442068437170441063105)
                  ·
                    rfl

theorem cell20_204725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_204725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204725 prefixEnd_204725 := by exact prefixLift 204725
  have htrace : WordTrace (prefixWord ++ tailWord_204725) baseStart_204725 baseEnd_204725 := by
    simpa [prefixWord, tailWord_204725, baseEnd_204725] using wordTrace_append hprefix tailTrace_204725
  have hstable : (prefixWord ++ tailWord_204725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204725).length < 2 ^ (prefixWord ++ tailWord_204725).sum := by decide
  have hdescent : baseEnd_204725 < baseStart_204725 := by decide
  rcases family_descends (prefixWord ++ tailWord_204725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204750 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_204750 : Nat := 118140960795 + 204750 * 2 ^ 59
def prefixEnd_204750 : Nat := 4983230072969 + 3 ^ 40 * 204750 * 2
def baseEnd_204750 : Nat := 93453479118381465229669

theorem tailTrace_204750 : CollatzResearch.WordTrace tailWord_204750 prefixEnd_204750 93453479118381465229669 := by
  unfold tailWord_204750
  simp only [CollatzResearch.WordTrace]
  refine ⟨933480751029149170140463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4978564005488795574082469 933480751029149170140463)
  ·
    refine ⟨1400221126543723755210695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 933480751029149170140463 1400221126543723755210695)
    ·
      refine ⟨2100331689815585632816043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1400221126543723755210695 2100331689815585632816043)
      ·
        refine ⟨3150497534723378449224065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2100331689815585632816043 3150497534723378449224065)
        ·
          refine ⟨2362873151042533836918049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3150497534723378449224065 2362873151042533836918049)
          ·
            refine ⟨1772154863281900377688537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2362873151042533836918049 1772154863281900377688537)
            ·
              refine ⟨1329116147461425283266403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1772154863281900377688537 1329116147461425283266403)
              ·
                refine ⟨1993674221192137924899605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329116147461425283266403 1993674221192137924899605)
                ·
                  refine ⟨93453479118381465229669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1993674221192137924899605 93453479118381465229669)
                  ·
                    rfl

theorem cell20_204750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_204750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204750 prefixEnd_204750 := by exact prefixLift 204750
  have htrace : WordTrace (prefixWord ++ tailWord_204750) baseStart_204750 baseEnd_204750 := by
    simpa [prefixWord, tailWord_204750, baseEnd_204750] using wordTrace_append hprefix tailTrace_204750
  have hstable : (prefixWord ++ tailWord_204750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204750).length < 2 ^ (prefixWord ++ tailWord_204750).sum := by decide
  have hdescent : baseEnd_204750 < baseStart_204750 := by decide
  rcases family_descends (prefixWord ++ tailWord_204750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204784 : List Nat := [2, 1, 1, 1, 3, 2, 6, 2, 2]
def baseStart_204784 : Nat := 118140960795 + 204784 * 2 ^ 59
def prefixEnd_204784 : Nat := 4983230072969 + 3 ^ 40 * 204784 * 2
def baseEnd_204784 : Nat := 93468997644828458096197

theorem tailTrace_204784 : CollatzResearch.WordTrace tailWord_204784 prefixEnd_204784 93468997644828458096197 := by
  unfold tailWord_204784
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734543045055008583930703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4979390726740011445240937 3734543045055008583930703)
  ·
    refine ⟨5601814567582512875896055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3734543045055008583930703 5601814567582512875896055)
    ·
      refine ⟨8402721851373769313844083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5601814567582512875896055 8402721851373769313844083)
      ·
        refine ⟨12604082777060653970766125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8402721851373769313844083 12604082777060653970766125)
        ·
          refine ⟨4726531041397745239037297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12604082777060653970766125 4726531041397745239037297)
          ·
            refine ⟨3544898281048308929277973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4726531041397745239037297 3544898281048308929277973)
            ·
              refine ⟨166167106924139481059905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3544898281048308929277973 166167106924139481059905)
              ·
                refine ⟨124625330193104610794929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166167106924139481059905 124625330193104610794929)
                ·
                  refine ⟨93468997644828458096197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124625330193104610794929 93468997644828458096197)
                  ·
                    rfl

theorem cell20_204784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_204784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204784 prefixEnd_204784 := by exact prefixLift 204784
  have htrace : WordTrace (prefixWord ++ tailWord_204784) baseStart_204784 baseEnd_204784 := by
    simpa [prefixWord, tailWord_204784, baseEnd_204784] using wordTrace_append hprefix tailTrace_204784
  have hstable : (prefixWord ++ tailWord_204784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204784).length < 2 ^ (prefixWord ++ tailWord_204784).sum := by decide
  have hdescent : baseEnd_204784 < baseStart_204784 := by decide
  rcases family_descends (prefixWord ++ tailWord_204784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204795 : List Nat := [1, 1, 1, 1, 1, 3, 7, 5]
def baseStart_204795 : Nat := 118140960795 + 204795 * 2 ^ 59
def prefixEnd_204795 : Nat := 4983230072969 + 3 ^ 40 * 204795 * 2
def baseEnd_204795 : Nat := 31158006114853769576495

theorem tailTrace_204795 : CollatzResearch.WordTrace tailWord_204795 prefixEnd_204795 31158006114853769576495 := by
  unfold tailWord_204795
  simp only [CollatzResearch.WordTrace]
  refine ⟨7469487293070166046511839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4979658195380110697674559 7469487293070166046511839)
  ·
    refine ⟨11204230939605249069767759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7469487293070166046511839 11204230939605249069767759)
    ·
      refine ⟨16806346409407873604651639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11204230939605249069767759 16806346409407873604651639)
      ·
        refine ⟨25209519614111810406977459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16806346409407873604651639 25209519614111810406977459)
        ·
          refine ⟨37814279421167715610466189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25209519614111810406977459 37814279421167715610466189)
          ·
            refine ⟨14180354782937893353924821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37814279421167715610466189 14180354782937893353924821)
            ·
              refine ⟨332352065225106875482613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14180354782937893353924821 332352065225106875482613)
              ·
                refine ⟨31158006114853769576495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 332352065225106875482613 31158006114853769576495)
                ·
                  rfl

theorem cell20_204795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_204795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204795 prefixEnd_204795 := by exact prefixLift 204795
  have htrace : WordTrace (prefixWord ++ tailWord_204795) baseStart_204795 baseEnd_204795 := by
    simpa [prefixWord, tailWord_204795, baseEnd_204795] using wordTrace_append hprefix tailTrace_204795
  have hstable : (prefixWord ++ tailWord_204795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204795).length < 2 ^ (prefixWord ++ tailWord_204795).sum := by decide
  have hdescent : baseEnd_204795 < baseStart_204795 := by decide
  rcases family_descends (prefixWord ++ tailWord_204795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204812 : List Nat := [2, 2, 1, 2, 3, 1, 5, 4]
def baseStart_204812 : Nat := 118140960795 + 204812 * 2 ^ 59
def prefixEnd_204812 : Nat := 4983230072969 + 3 ^ 40 * 204812 * 2
def baseEnd_204812 : Nat := 31160592535928268387583

theorem tailTrace_204812 : CollatzResearch.WordTrace tailWord_204812 prefixEnd_204812 31160592535928268387583 := by
  unfold tailWord_204812
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735053667004288974940345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4980071556005718633253793 3735053667004288974940345)
  ·
    refine ⟨2801290250253216731205259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3735053667004288974940345 2801290250253216731205259)
    ·
      refine ⟨4201935375379825096807889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2801290250253216731205259 4201935375379825096807889)
      ·
        refine ⟨3151451531534868822605917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4201935375379825096807889 3151451531534868822605917)
        ·
          refine ⟨1181794324325575808477219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3151451531534868822605917 1181794324325575808477219)
          ·
            refine ⟨1772691486488363712715829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181794324325575808477219 1772691486488363712715829)
            ·
              refine ⟨166189826858284098067109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1772691486488363712715829 166189826858284098067109)
              ·
                refine ⟨31160592535928268387583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166189826858284098067109 31160592535928268387583)
                ·
                  rfl

theorem cell20_204812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_204812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204812 prefixEnd_204812 := by exact prefixLift 204812
  have htrace : WordTrace (prefixWord ++ tailWord_204812) baseStart_204812 baseEnd_204812 := by
    simpa [prefixWord, tailWord_204812, baseEnd_204812] using wordTrace_append hprefix tailTrace_204812
  have hstable : (prefixWord ++ tailWord_204812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204812).length < 2 ^ (prefixWord ++ tailWord_204812).sum := by decide
  have hdescent : baseEnd_204812 < baseStart_204812 := by decide
  rcases family_descends (prefixWord ++ tailWord_204812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204836 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 5]
def baseStart_204836 : Nat := 118140960795 + 204836 * 2 ^ 59
def prefixEnd_204836 : Nat := 4983230072969 + 3 ^ 40 * 204836 * 2
def baseEnd_204836 : Nat := 93492731861747388362651

theorem tailTrace_204836 : CollatzResearch.WordTrace tailWord_204836 prefixEnd_204836 93492731861747388362651 := by
  unfold tailWord_204836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735491342960815024377181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4980655123947753365836241 3735491342960815024377181)
  ·
    refine ⟨1400809253610305634141443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3735491342960815024377181 1400809253610305634141443)
    ·
      refine ⟨2101213880415458451212165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1400809253610305634141443 2101213880415458451212165)
      ·
        refine ⟨393977602577898459602281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2101213880415458451212165 393977602577898459602281)
        ·
          refine ⟨295483201933423844701711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393977602577898459602281 295483201933423844701711)
          ·
            refine ⟨443224802900135767052567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295483201933423844701711 443224802900135767052567)
            ·
              refine ⟨664837204350203650578851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443224802900135767052567 664837204350203650578851)
              ·
                refine ⟨997255806525305475868277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664837204350203650578851 997255806525305475868277)
                ·
                  refine ⟨93492731861747388362651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 997255806525305475868277 93492731861747388362651)
                  ·
                    rfl

theorem cell20_204836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_204836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204836 prefixEnd_204836 := by exact prefixLift 204836
  have htrace : WordTrace (prefixWord ++ tailWord_204836) baseStart_204836 baseEnd_204836 := by
    simpa [prefixWord, tailWord_204836, baseEnd_204836] using wordTrace_append hprefix tailTrace_204836
  have hstable : (prefixWord ++ tailWord_204836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204836).length < 2 ^ (prefixWord ++ tailWord_204836).sum := by decide
  have hdescent : baseEnd_204836 < baseStart_204836 := by decide
  rcases family_descends (prefixWord ++ tailWord_204836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204864 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_204864 : Nat := 118140960795 + 204864 * 2 ^ 59
def prefixEnd_204864 : Nat := 4983230072969 + 3 ^ 40 * 204864 * 2
def baseEnd_204864 : Nat := 93505511824703735429203

theorem tailTrace_204864 : CollatzResearch.WordTrace tailWord_204864 prefixEnd_204864 93505511824703735429203 := by
  unfold tailWord_204864
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736001964910095415386823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4981335953213460553849097 3736001964910095415386823)
  ·
    refine ⟨5604002947365143123080235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3736001964910095415386823 5604002947365143123080235)
    ·
      refine ⟨8406004421047714684620353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5604002947365143123080235 8406004421047714684620353)
      ·
        refine ⟨6304503315785786013465265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8406004421047714684620353 6304503315785786013465265)
        ·
          refine ⟨4728377486839339510098949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6304503315785786013465265 4728377486839339510098949)
          ·
            refine ⟨886570778782376158143553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4728377486839339510098949 886570778782376158143553)
            ·
              refine ⟨664928084086782118607665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886570778782376158143553 664928084086782118607665)
              ·
                refine ⟨498696063065086588955749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664928084086782118607665 498696063065086588955749)
                ·
                  refine ⟨93505511824703735429203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498696063065086588955749 93505511824703735429203)
                  ·
                    rfl

theorem cell20_204864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_204864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204864 prefixEnd_204864 := by exact prefixLift 204864
  have htrace : WordTrace (prefixWord ++ tailWord_204864) baseStart_204864 baseEnd_204864 := by
    simpa [prefixWord, tailWord_204864, baseEnd_204864] using wordTrace_append hprefix tailTrace_204864
  have hstable : (prefixWord ++ tailWord_204864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204864).length < 2 ^ (prefixWord ++ tailWord_204864).sum := by decide
  have hdescent : baseEnd_204864 < baseStart_204864 := by decide
  rcases family_descends (prefixWord ++ tailWord_204864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204871 : List Nat := [1, 1, 4, 1, 3, 1, 3, 6]
def baseStart_204871 : Nat := 118140960795 + 204871 * 2 ^ 59
def prefixEnd_204871 : Nat := 4983230072969 + 3 ^ 40 * 204871 * 2
def baseEnd_204871 : Nat := 31169568938480940731947

theorem tailTrace_204871 : CollatzResearch.WordTrace tailWord_204871 prefixEnd_204871 31169568938480940731947 := by
  unfold tailWord_204871
  simp only [CollatzResearch.WordTrace]
  refine ⟨7472259240794831026278467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4981506160529887350852311 7472259240794831026278467)
  ·
    refine ⟨11208388861192246539417701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7472259240794831026278467 11208388861192246539417701)
    ·
      refine ⟨2101572911473546226140819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11208388861192246539417701 2101572911473546226140819)
      ·
        refine ⟨3152359367210319339211229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2101572911473546226140819 3152359367210319339211229)
        ·
          refine ⟨1182134762703869752204211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3152359367210319339211229 1182134762703869752204211)
          ·
            refine ⟨1773202144055804628306317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182134762703869752204211 1773202144055804628306317)
            ·
              refine ⟨664950804020926735614869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1773202144055804628306317 664950804020926735614869)
              ·
                refine ⟨31169568938480940731947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 664950804020926735614869 31169568938480940731947)
                ·
                  rfl

theorem cell20_204871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_204871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204871 prefixEnd_204871 := by exact prefixLift 204871
  have htrace : WordTrace (prefixWord ++ tailWord_204871) baseStart_204871 baseEnd_204871 := by
    simpa [prefixWord, tailWord_204871, baseEnd_204871] using wordTrace_append hprefix tailTrace_204871
  have hstable : (prefixWord ++ tailWord_204871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204871).length < 2 ^ (prefixWord ++ tailWord_204871).sum := by decide
  have hdescent : baseEnd_204871 < baseStart_204871 := by decide
  rcases family_descends (prefixWord ++ tailWord_204871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204894 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_204894 : Nat := 118140960795 + 204894 * 2 ^ 59
def prefixEnd_204894 : Nat := 4983230072969 + 3 ^ 40 * 204894 * 2
def baseEnd_204894 : Nat := 93519204642156964429081

theorem tailTrace_204894 : CollatzResearch.WordTrace tailWord_204894 prefixEnd_204894 93519204642156964429081 := by
  unfold tailWord_204894
  simp only [CollatzResearch.WordTrace]
  refine ⟨934137264963938244295717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4982065413141003969577157 934137264963938244295717)
  ·
    refine ⟨175150737180738420805447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 934137264963938244295717 175150737180738420805447)
    ·
      refine ⟨262726105771107631208171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175150737180738420805447 262726105771107631208171)
      ·
        refine ⟨394089158656661446812257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262726105771107631208171 394089158656661446812257)
        ·
          refine ⟨295566868992496085109193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394089158656661446812257 295566868992496085109193)
          ·
            refine ⟨221675151744372063831895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295566868992496085109193 221675151744372063831895)
            ·
              refine ⟨332512727616558095747843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221675151744372063831895 332512727616558095747843)
              ·
                refine ⟨498769091424837143621765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332512727616558095747843 498769091424837143621765)
                ·
                  refine ⟨93519204642156964429081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498769091424837143621765 93519204642156964429081)
                  ·
                    rfl

theorem cell20_204894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_204894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204894 prefixEnd_204894 := by exact prefixLift 204894
  have htrace : WordTrace (prefixWord ++ tailWord_204894) baseStart_204894 baseEnd_204894 := by
    simpa [prefixWord, tailWord_204894, baseEnd_204894] using wordTrace_append hprefix tailTrace_204894
  have hstable : (prefixWord ++ tailWord_204894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204894).length < 2 ^ (prefixWord ++ tailWord_204894).sum := by decide
  have hdescent : baseEnd_204894 < baseStart_204894 := by decide
  rcases family_descends (prefixWord ++ tailWord_204894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204912 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 3]
def baseStart_204912 : Nat := 118140960795 + 204912 * 2 ^ 59
def prefixEnd_204912 : Nat := 4983230072969 + 3 ^ 40 * 204912 * 2
def baseEnd_204912 : Nat := 93527420332628901829007

theorem tailTrace_204912 : CollatzResearch.WordTrace tailWord_204912 prefixEnd_204912 93527420332628901829007 := by
  unfold tailWord_204912
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736877316823147514260495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4982503089097530019013993 3736877316823147514260495)
  ·
    refine ⟨5605315975234721271390743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3736877316823147514260495 5605315975234721271390743)
    ·
      refine ⟨8407973962852081907086115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605315975234721271390743 8407973962852081907086115)
      ·
        refine ⟨12611960944278122860629173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8407973962852081907086115 12611960944278122860629173)
        ·
          refine ⟨1182371338526074018183985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12611960944278122860629173 1182371338526074018183985)
          ·
            refine ⟨886778503894555513637989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1182371338526074018183985 886778503894555513637989)
            ·
              refine ⟨166270969480229158807123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 886778503894555513637989 166270969480229158807123)
              ·
                refine ⟨249406454220343738210685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166270969480229158807123 249406454220343738210685)
                ·
                  refine ⟨93527420332628901829007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249406454220343738210685 93527420332628901829007)
                  ·
                    rfl

theorem cell20_204912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_204912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204912 prefixEnd_204912 := by exact prefixLift 204912
  have htrace : WordTrace (prefixWord ++ tailWord_204912) baseStart_204912 baseEnd_204912 := by
    simpa [prefixWord, tailWord_204912, baseEnd_204912] using wordTrace_append hprefix tailTrace_204912
  have hstable : (prefixWord ++ tailWord_204912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204912).length < 2 ^ (prefixWord ++ tailWord_204912).sum := by decide
  have hdescent : baseEnd_204912 < baseStart_204912 := by decide
  rcases family_descends (prefixWord ++ tailWord_204912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204978 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_204978 : Nat := 118140960795 + 204978 * 2 ^ 59
def prefixEnd_204978 : Nat := 4983230072969 + 3 ^ 40 * 204978 * 2
def baseEnd_204978 : Nat := 93557544531026005628737

theorem tailTrace_204978 : CollatzResearch.WordTrace tailWord_204978 prefixEnd_204978 93557544531026005628737 := by
  unfold tailWord_204978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869040462851797075105897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4984107900938125533615725 1869040462851797075105897)
  ·
    refine ⟨1401780347138847806329423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1869040462851797075105897 1401780347138847806329423)
    ·
      refine ⟨2102670520708271709494135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1401780347138847806329423 2102670520708271709494135)
      ·
        refine ⟨3154005781062407564241203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102670520708271709494135 3154005781062407564241203)
        ·
          refine ⟨4731008671593611346361805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154005781062407564241203 4731008671593611346361805)
          ·
            refine ⟨1774128251847604254885677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4731008671593611346361805 1774128251847604254885677)
            ·
              refine ⟨665298094442851595582129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1774128251847604254885677 665298094442851595582129)
              ·
                refine ⟨498973570832138696686597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665298094442851595582129 498973570832138696686597)
                ·
                  refine ⟨93557544531026005628737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498973570832138696686597 93557544531026005628737)
                  ·
                    rfl

theorem cell20_204978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_204978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_204978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_204978 prefixEnd_204978 := by exact prefixLift 204978
  have htrace : WordTrace (prefixWord ++ tailWord_204978) baseStart_204978 baseEnd_204978 := by
    simpa [prefixWord, tailWord_204978, baseEnd_204978] using wordTrace_append hprefix tailTrace_204978
  have hstable : (prefixWord ++ tailWord_204978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204978).length < 2 ^ (prefixWord ++ tailWord_204978).sum := by decide
  have hdescent : baseEnd_204978 < baseStart_204978 := by decide
  rcases family_descends (prefixWord ++ tailWord_204978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205009 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 3]
def baseStart_205009 : Nat := 118140960795 + 205009 * 2 ^ 59
def prefixEnd_205009 : Nat := 4983230072969 + 3 ^ 40 * 205009 * 2
def baseEnd_205009 : Nat := 93571693775727675595277

theorem tailTrace_205009 : CollatzResearch.WordTrace tailWord_205009 prefixEnd_205009 93571693775727675595277 := by
  unfold tailWord_205009
  simp only [CollatzResearch.WordTrace]
  refine ⟨7477292514294880594802081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4984861676196587063201387 7477292514294880594802081)
  ·
    refine ⟨5607969385721160446101561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7477292514294880594802081 5607969385721160446101561)
    ·
      refine ⟨4205977039290870334576171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5607969385721160446101561 4205977039290870334576171)
      ·
        refine ⟨6308965558936305501864257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205977039290870334576171 6308965558936305501864257)
        ·
          refine ⟨4731724169202229126398193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6308965558936305501864257 4731724169202229126398193)
          ·
            refine ⟨3548793126901671844798645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4731724169202229126398193 3548793126901671844798645)
            ·
              refine ⟨332699355647031735449873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3548793126901671844798645 332699355647031735449873)
              ·
                refine ⟨249524516735273801587405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332699355647031735449873 249524516735273801587405)
                ·
                  refine ⟨93571693775727675595277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249524516735273801587405 93571693775727675595277)
                  ·
                    rfl

theorem cell20_205009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_205009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205009 prefixEnd_205009 := by exact prefixLift 205009
  have htrace : WordTrace (prefixWord ++ tailWord_205009) baseStart_205009 baseEnd_205009 := by
    simpa [prefixWord, tailWord_205009, baseEnd_205009] using wordTrace_append hprefix tailTrace_205009
  have hstable : (prefixWord ++ tailWord_205009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205009).length < 2 ^ (prefixWord ++ tailWord_205009).sum := by decide
  have hdescent : baseEnd_205009 < baseStart_205009 := by decide
  rcases family_descends (prefixWord ++ tailWord_205009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205016 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_205016 : Nat := 118140960795 + 205016 * 2 ^ 59
def prefixEnd_205016 : Nat := 4983230072969 + 3 ^ 40 * 205016 * 2
def baseEnd_205016 : Nat := 93574888766466762361915

theorem tailTrace_205016 : CollatzResearch.WordTrace tailWord_205016 prefixEnd_205016 93574888766466762361915 := by
  unfold tailWord_205016
  simp only [CollatzResearch.WordTrace]
  refine ⟨3738773912634760395153451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4985031883513013860204601 3738773912634760395153451)
  ·
    refine ⟨5608160868952140592730177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3738773912634760395153451 5608160868952140592730177)
    ·
      refine ⟨4206120651714105444547633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5608160868952140592730177 4206120651714105444547633)
      ·
        refine ⟨3154590488785579083410725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4206120651714105444547633 3154590488785579083410725)
        ·
          refine ⟨591485716647296078139511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3154590488785579083410725 591485716647296078139511)
          ·
            refine ⟨887228574970944117209267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591485716647296078139511 887228574970944117209267)
            ·
              refine ⟨1330842862456416175813901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887228574970944117209267 1330842862456416175813901)
              ·
                refine ⟨499066073421156065930213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1330842862456416175813901 499066073421156065930213)
                ·
                  refine ⟨93574888766466762361915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 499066073421156065930213 93574888766466762361915)
                  ·
                    rfl

theorem cell20_205016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_205016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205016 prefixEnd_205016 := by exact prefixLift 205016
  have htrace : WordTrace (prefixWord ++ tailWord_205016) baseStart_205016 baseEnd_205016 := by
    simpa [prefixWord, tailWord_205016, baseEnd_205016] using wordTrace_append hprefix tailTrace_205016
  have hstable : (prefixWord ++ tailWord_205016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205016).length < 2 ^ (prefixWord ++ tailWord_205016).sum := by decide
  have hdescent : baseEnd_205016 < baseStart_205016 := by decide
  rcases family_descends (prefixWord ++ tailWord_205016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205050 : List Nat := [3, 1, 1, 1, 1, 7, 1, 3, 2]
def baseStart_205050 : Nat := 118140960795 + 205050 * 2 ^ 59
def prefixEnd_205050 : Nat := 4983230072969 + 3 ^ 40 * 205050 * 2
def baseEnd_205050 : Nat := 93590407292913755228443

theorem tailTrace_205050 : CollatzResearch.WordTrace tailWord_205050 prefixEnd_205050 93590407292913755228443 := by
  unfold tailWord_205050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869696976786586149261151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4985858604764229731363069 1869696976786586149261151)
  ·
    refine ⟨2804545465179879223891727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1869696976786586149261151 2804545465179879223891727)
    ·
      refine ⟨4206818197769818835837591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2804545465179879223891727 4206818197769818835837591)
      ·
        refine ⟨6310227296654728253756387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4206818197769818835837591 6310227296654728253756387)
        ·
          refine ⟨9465340944982092380634581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310227296654728253756387 9465340944982092380634581)
          ·
            refine ⟨221843928398017790171123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9465340944982092380634581 221843928398017790171123)
            ·
              refine ⟨332765892597026685256685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221843928398017790171123 332765892597026685256685)
              ·
                refine ⟨124787209723885006971257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332765892597026685256685 124787209723885006971257)
                ·
                  refine ⟨93590407292913755228443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124787209723885006971257 93590407292913755228443)
                  ·
                    rfl

theorem cell20_205050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_205050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205050 prefixEnd_205050 := by exact prefixLift 205050
  have htrace : WordTrace (prefixWord ++ tailWord_205050) baseStart_205050 baseEnd_205050 := by
    simpa [prefixWord, tailWord_205050, baseEnd_205050] using wordTrace_append hprefix tailTrace_205050
  have hstable : (prefixWord ++ tailWord_205050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205050).length < 2 ^ (prefixWord ++ tailWord_205050).sum := by decide
  have hdescent : baseEnd_205050 < baseStart_205050 := by decide
  rcases family_descends (prefixWord ++ tailWord_205050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205068 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_205068 : Nat := 118140960795 + 205068 * 2 ^ 59
def prefixEnd_205068 : Nat := 4983230072969 + 3 ^ 40 * 205068 * 2
def baseEnd_205068 : Nat := 93598622983385692628369

theorem tailTrace_205068 : CollatzResearch.WordTrace tailWord_205068 prefixEnd_205068 93598622983385692628369 := by
  unfold tailWord_205068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3739722210540566835599929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4986296280720755780799905 3739722210540566835599929)
  ·
    refine ⟨2804791657905425126699947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3739722210540566835599929 2804791657905425126699947)
    ·
      refine ⟨4207187486858137690049921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2804791657905425126699947 4207187486858137690049921)
      ·
        refine ⟨3155390615143603267537441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4207187486858137690049921 3155390615143603267537441)
        ·
          refine ⟨2366542961357702450653081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3155390615143603267537441 2366542961357702450653081)
          ·
            refine ⟨1774907221018276837989811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2366542961357702450653081 1774907221018276837989811)
            ·
              refine ⟨2662360831527415256984717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774907221018276837989811 2662360831527415256984717)
              ·
                refine ⟨998385311822780721369269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2662360831527415256984717 998385311822780721369269)
                ·
                  refine ⟨93598622983385692628369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 998385311822780721369269 93598622983385692628369)
                  ·
                    rfl

theorem cell20_205068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_205068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205068 prefixEnd_205068 := by exact prefixLift 205068
  have htrace : WordTrace (prefixWord ++ tailWord_205068) baseStart_205068 baseEnd_205068 := by
    simpa [prefixWord, tailWord_205068, baseEnd_205068] using wordTrace_append hprefix tailTrace_205068
  have hstable : (prefixWord ++ tailWord_205068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205068).length < 2 ^ (prefixWord ++ tailWord_205068).sum := by decide
  have hdescent : baseEnd_205068 < baseStart_205068 := by decide
  rcases family_descends (prefixWord ++ tailWord_205068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205109 : List Nat := [1, 3, 3, 1, 2, 1, 2, 5, 2]
def baseStart_205109 : Nat := 118140960795 + 205109 * 2 ^ 59
def prefixEnd_205109 : Nat := 4983230072969 + 3 ^ 40 * 205109 * 2
def baseEnd_205109 : Nat := 93617336500571772261535

theorem tailTrace_205109 : CollatzResearch.WordTrace tailWord_205109 prefixEnd_205109 93617336500571772261535 := by
  unfold tailWord_205109
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480939813932597673442381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4987293209288398448961587 7480939813932597673442381)
  ·
    refine ⟨2805352430224724127540893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7480939813932597673442381 2805352430224724127540893)
    ·
      refine ⟨1052007161334271547827835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2805352430224724127540893 1052007161334271547827835)
      ·
        refine ⟨1578010742001407321741753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052007161334271547827835 1578010742001407321741753)
        ·
          refine ⟨1183508056501055491306315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1578010742001407321741753 1183508056501055491306315)
          ·
            refine ⟨1775262084751583236959473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183508056501055491306315 1775262084751583236959473)
            ·
              refine ⟨1331446563563687427719605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1775262084751583236959473 1331446563563687427719605)
              ·
                refine ⟨124823115334095696348713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1331446563563687427719605 124823115334095696348713)
                ·
                  refine ⟨93617336500571772261535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124823115334095696348713 93617336500571772261535)
                  ·
                    rfl

theorem cell20_205109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_205109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205109 prefixEnd_205109 := by exact prefixLift 205109
  have htrace : WordTrace (prefixWord ++ tailWord_205109) baseStart_205109 baseEnd_205109 := by
    simpa [prefixWord, tailWord_205109, baseEnd_205109] using wordTrace_append hprefix tailTrace_205109
  have hstable : (prefixWord ++ tailWord_205109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205109).length < 2 ^ (prefixWord ++ tailWord_205109).sum := by decide
  have hdescent : baseEnd_205109 < baseStart_205109 := by decide
  rcases family_descends (prefixWord ++ tailWord_205109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205137 : List Nat := [1, 2, 2, 1, 4, 2, 3, 5]
def baseStart_205137 : Nat := 118140960795 + 205137 * 2 ^ 59
def prefixEnd_205137 : Nat := 4983230072969 + 3 ^ 40 * 205137 * 2
def baseEnd_205137 : Nat := 31210038821176039776029

theorem tailTrace_205137 : CollatzResearch.WordTrace tailWord_205137 prefixEnd_205137 31210038821176039776029 := by
  unfold tailWord_205137
  simp only [CollatzResearch.WordTrace]
  refine ⟨7481961057831158455461665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4987974038554105636974443 7481961057831158455461665)
  ·
    refine ⟨5611470793373368841596249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7481961057831158455461665 5611470793373368841596249)
    ·
      refine ⟨4208603095030026631197187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5611470793373368841596249 4208603095030026631197187)
      ·
        refine ⟨6312904642545039946795781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4208603095030026631197187 6312904642545039946795781)
        ·
          refine ⟨1183669620477194990024209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6312904642545039946795781 1183669620477194990024209)
          ·
            refine ⟨887752215357896242518157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1183669620477194990024209 887752215357896242518157)
            ·
              refine ⟨332907080759211090944309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 887752215357896242518157 332907080759211090944309)
              ·
                refine ⟨31210038821176039776029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 332907080759211090944309 31210038821176039776029)
                ·
                  rfl

theorem cell20_205137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_205137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205137 prefixEnd_205137 := by exact prefixLift 205137
  have htrace : WordTrace (prefixWord ++ tailWord_205137) baseStart_205137 baseEnd_205137 := by
    simpa [prefixWord, tailWord_205137, baseEnd_205137] using wordTrace_append hprefix tailTrace_205137
  have hstable : (prefixWord ++ tailWord_205137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205137).length < 2 ^ (prefixWord ++ tailWord_205137).sum := by decide
  have hdescent : baseEnd_205137 < baseStart_205137 := by decide
  rcases family_descends (prefixWord ++ tailWord_205137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205151 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_205151 : Nat := 118140960795 + 205151 * 2 ^ 59
def prefixEnd_205151 : Nat := 4983230072969 + 3 ^ 40 * 205151 * 2
def baseEnd_205151 : Nat := 93636506445006292861363

theorem tailTrace_205151 : CollatzResearch.WordTrace tailWord_205151 prefixEnd_205151 93636506445006292861363 := by
  unfold tailWord_205151
  simp only [CollatzResearch.WordTrace]
  refine ⟨7482471679780438846471307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4988314453186959230980871 7482471679780438846471307)
  ·
    refine ⟨11223707519670658269706961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7482471679780438846471307 11223707519670658269706961)
    ·
      refine ⟨8417780639752993702280221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11223707519670658269706961 8417780639752993702280221)
      ·
        refine ⟨3156667739907372638355083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8417780639752993702280221 3156667739907372638355083)
        ·
          refine ⟨4735001609861058957532625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156667739907372638355083 4735001609861058957532625)
          ·
            refine ⟨3551251207395794218149469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4735001609861058957532625 3551251207395794218149469)
            ·
              refine ⟨1331719202773422831806051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3551251207395794218149469 1331719202773422831806051)
              ·
                refine ⟨1997578804160134247709077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331719202773422831806051 1997578804160134247709077)
                ·
                  refine ⟨93636506445006292861363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1997578804160134247709077 93636506445006292861363)
                  ·
                    rfl

theorem cell20_205151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_205151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205151 prefixEnd_205151 := by exact prefixLift 205151
  have htrace : WordTrace (prefixWord ++ tailWord_205151) baseStart_205151 baseEnd_205151 := by
    simpa [prefixWord, tailWord_205151, baseEnd_205151] using wordTrace_append hprefix tailTrace_205151
  have hstable : (prefixWord ++ tailWord_205151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205151).length < 2 ^ (prefixWord ++ tailWord_205151).sum := by decide
  have hdescent : baseEnd_205151 < baseStart_205151 := by decide
  rcases family_descends (prefixWord ++ tailWord_205151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205164 : List Nat := [2, 2, 1, 1, 6, 1, 2, 3, 2]
def baseStart_205164 : Nat := 118140960795 + 205164 * 2 ^ 59
def prefixEnd_205164 : Nat := 4983230072969 + 3 ^ 40 * 205164 * 2
def baseEnd_205164 : Nat := 93642439999236025427977

theorem tailTrace_205164 : CollatzResearch.WordTrace tailWord_205164 prefixEnd_205164 93642439999236025427977 := by
  unfold tailWord_205164
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741472914366671033347273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4988630552488894711129697 3741472914366671033347273)
  ·
    refine ⟨2806104685775003275010455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3741472914366671033347273 2806104685775003275010455)
    ·
      refine ⟨4209157028662504912515683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2806104685775003275010455 4209157028662504912515683)
      ·
        refine ⟨6313735542993757368773525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4209157028662504912515683 6313735542993757368773525)
        ·
          refine ⟨295956353577832376661259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6313735542993757368773525 295956353577832376661259)
          ·
            refine ⟨443934530366748564991889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295956353577832376661259 443934530366748564991889)
            ·
              refine ⟨332950897775061423743917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443934530366748564991889 332950897775061423743917)
              ·
                refine ⟨124856586665648033903969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332950897775061423743917 124856586665648033903969)
                ·
                  refine ⟨93642439999236025427977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124856586665648033903969 93642439999236025427977)
                  ·
                    rfl

theorem cell20_205164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_205164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205164 prefixEnd_205164 := by exact prefixLift 205164
  have htrace : WordTrace (prefixWord ++ tailWord_205164) baseStart_205164 baseEnd_205164 := by
    simpa [prefixWord, tailWord_205164, baseEnd_205164] using wordTrace_append hprefix tailTrace_205164
  have hstable : (prefixWord ++ tailWord_205164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205164).length < 2 ^ (prefixWord ++ tailWord_205164).sum := by decide
  have hdescent : baseEnd_205164 < baseStart_205164 := by decide
  rcases family_descends (prefixWord ++ tailWord_205164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205174 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_205174 : Nat := 118140960795 + 205174 * 2 ^ 59
def prefixEnd_205174 : Nat := 4983230072969 + 3 ^ 40 * 205174 * 2
def baseEnd_205174 : Nat := 93647004271720435094603

theorem tailTrace_205174 : CollatzResearch.WordTrace tailWord_205174 prefixEnd_205174 93647004271720435094603 := by
  unfold tailWord_205174
  simp only [CollatzResearch.WordTrace]
  refine ⟨467706909918569610909911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4988873705798075849705717 467706909918569610909911)
  ·
    refine ⟨701560364877854416364867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 467706909918569610909911 701560364877854416364867)
    ·
      refine ⟨1052340547316781624547301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701560364877854416364867 1052340547316781624547301)
      ·
        refine ⟨197313852621896554602619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1052340547316781624547301 197313852621896554602619)
        ·
          refine ⟨295970778932844831903929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197313852621896554602619 295970778932844831903929)
          ·
            refine ⟨221978084199633623927947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295970778932844831903929 221978084199633623927947)
            ·
              refine ⟨332967126299450435891921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221978084199633623927947 332967126299450435891921)
              ·
                refine ⟨249725344724587826918941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332967126299450435891921 249725344724587826918941)
                ·
                  refine ⟨93647004271720435094603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249725344724587826918941 93647004271720435094603)
                  ·
                    rfl

theorem cell20_205174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_205174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205174 prefixEnd_205174 := by exact prefixLift 205174
  have htrace : WordTrace (prefixWord ++ tailWord_205174) baseStart_205174 baseEnd_205174 := by
    simpa [prefixWord, tailWord_205174, baseEnd_205174] using wordTrace_append hprefix tailTrace_205174
  have hstable : (prefixWord ++ tailWord_205174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205174).length < 2 ^ (prefixWord ++ tailWord_205174).sum := by decide
  have hdescent : baseEnd_205174 < baseStart_205174 := by decide
  rcases family_descends (prefixWord ++ tailWord_205174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205185 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 4]
def baseStart_205185 : Nat := 118140960795 + 205185 * 2 ^ 59
def prefixEnd_205185 : Nat := 4983230072969 + 3 ^ 40 * 205185 * 2
def baseEnd_205185 : Nat := 93652024971453285727891

theorem tailTrace_205185 : CollatzResearch.WordTrace tailWord_205185 prefixEnd_205185 93652024971453285727891 := by
  unfold tailWord_205185
  simp only [CollatzResearch.WordTrace]
  refine ⟨7483711761657262653209009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4989141174438175102139339 7483711761657262653209009)
  ·
    refine ⟨5612783821242946989906757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7483711761657262653209009 5612783821242946989906757)
    ·
      refine ⟨1052396966483052560607517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5612783821242946989906757 1052396966483052560607517)
      ·
        refine ⟨394648862431144710227819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1052396966483052560607517 394648862431144710227819)
        ·
          refine ⟨591973293646717065341729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394648862431144710227819 591973293646717065341729)
          ·
            refine ⟨443979970235037799006297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591973293646717065341729 443979970235037799006297)
            ·
              refine ⟨332984977676278349254723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443979970235037799006297 332984977676278349254723)
              ·
                refine ⟨499477466514417523882085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332984977676278349254723 499477466514417523882085)
                ·
                  refine ⟨93652024971453285727891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 499477466514417523882085 93652024971453285727891)
                  ·
                    rfl

theorem cell20_205185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_205185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205185 prefixEnd_205185 := by exact prefixLift 205185
  have htrace : WordTrace (prefixWord ++ tailWord_205185) baseStart_205185 baseEnd_205185 := by
    simpa [prefixWord, tailWord_205185, baseEnd_205185] using wordTrace_append hprefix tailTrace_205185
  have hstable : (prefixWord ++ tailWord_205185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205185).length < 2 ^ (prefixWord ++ tailWord_205185).sum := by decide
  have hdescent : baseEnd_205185 < baseStart_205185 := by decide
  rcases family_descends (prefixWord ++ tailWord_205185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205220 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_205220 : Nat := 118140960795 + 205220 * 2 ^ 59
def prefixEnd_205220 : Nat := 4983230072969 + 3 ^ 40 * 205220 * 2
def baseEnd_205220 : Nat := 93667999925148719561081

theorem tailTrace_205220 : CollatzResearch.WordTrace tailWord_205220 prefixEnd_205220 93667999925148719561081 := by
  unfold tailWord_205220
  simp only [CollatzResearch.WordTrace]
  refine ⟨3742494158265231815366557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4989992211020309087155409 3742494158265231815366557)
  ·
    refine ⟨1403435309349461930762459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3742494158265231815366557 1403435309349461930762459)
    ·
      refine ⟨2105152964024192896143689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403435309349461930762459 2105152964024192896143689)
      ·
        refine ⟨1578864723018144672107767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2105152964024192896143689 1578864723018144672107767)
        ·
          refine ⟨2368297084527217008161651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578864723018144672107767 2368297084527217008161651)
          ·
            refine ⟨3552445626790825512242477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368297084527217008161651 3552445626790825512242477)
            ·
              refine ⟨1332167110046559567090929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3552445626790825512242477 1332167110046559567090929)
              ·
                refine ⟨999125332534919675318197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332167110046559567090929 999125332534919675318197)
                ·
                  refine ⟨93667999925148719561081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 999125332534919675318197 93667999925148719561081)
                  ·
                    rfl

theorem cell20_205220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_205220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205220 prefixEnd_205220 := by exact prefixLift 205220
  have htrace : WordTrace (prefixWord ++ tailWord_205220) baseStart_205220 baseEnd_205220 := by
    simpa [prefixWord, tailWord_205220, baseEnd_205220] using wordTrace_append hprefix tailTrace_205220
  have hstable : (prefixWord ++ tailWord_205220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205220).length < 2 ^ (prefixWord ++ tailWord_205220).sum := by decide
  have hdescent : baseEnd_205220 < baseStart_205220 := by decide
  rcases family_descends (prefixWord ++ tailWord_205220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205226 : List Nat := [3, 1, 6, 1, 1, 2, 6]
def baseStart_205226 : Nat := 118140960795 + 205226 * 2 ^ 59
def prefixEnd_205226 : Nat := 4983230072969 + 3 ^ 40 * 205226 * 2
def baseEnd_205226 : Nat := 10407859832071040595673

theorem tailTrace_205226 : CollatzResearch.WordTrace tailWord_205226 prefixEnd_205226 10407859832071040595673 := by
  unfold tailWord_205226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871301788627181663862883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4990138103005817770301021 1871301788627181663862883)
  ·
    refine ⟨2806952682940772495794325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871301788627181663862883 2806952682940772495794325)
    ·
      refine ⟨131575907012848710740359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2806952682940772495794325 131575907012848710740359)
      ·
        refine ⟨197363860519273066110539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131575907012848710740359 197363860519273066110539)
        ·
          refine ⟨296045790778909599165809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197363860519273066110539 296045790778909599165809)
          ·
            refine ⟨222034343084182199374357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296045790778909599165809 222034343084182199374357)
            ·
              refine ⟨10407859832071040595673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222034343084182199374357 10407859832071040595673)
              ·
                rfl

theorem cell20_205226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 6].length) (baseStart_205226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205226 prefixEnd_205226 := by exact prefixLift 205226
  have htrace : WordTrace (prefixWord ++ tailWord_205226) baseStart_205226 baseEnd_205226 := by
    simpa [prefixWord, tailWord_205226, baseEnd_205226] using wordTrace_append hprefix tailTrace_205226
  have hstable : (prefixWord ++ tailWord_205226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205226).length < 2 ^ (prefixWord ++ tailWord_205226).sum := by decide
  have hdescent : baseEnd_205226 < baseStart_205226 := by decide
  rcases family_descends (prefixWord ++ tailWord_205226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205236 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 4]
def baseStart_205236 : Nat := 118140960795 + 205236 * 2 ^ 59
def prefixEnd_205236 : Nat := 4983230072969 + 3 ^ 40 * 205236 * 2
def baseEnd_205236 : Nat := 93675302761123775027683

theorem tailTrace_205236 : CollatzResearch.WordTrace tailWord_205236 prefixEnd_205236 93675302761123775027683 := by
  unfold tailWord_205236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3742785942236249181657781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4990381256314998908877041 3742785942236249181657781)
  ·
    refine ⟨350886182084648360780417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3742785942236249181657781 350886182084648360780417)
    ·
      refine ⟨263164636563486270585313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350886182084648360780417 263164636563486270585313)
      ·
        refine ⟨197373477422614702938985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263164636563486270585313 197373477422614702938985)
        ·
          refine ⟨148030108066961027204239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197373477422614702938985 148030108066961027204239)
          ·
            refine ⟨222045162100441540806359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148030108066961027204239 222045162100441540806359)
            ·
              refine ⟨333067743150662311209539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222045162100441540806359 333067743150662311209539)
              ·
                refine ⟨499601614725993466814309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333067743150662311209539 499601614725993466814309)
                ·
                  refine ⟨93675302761123775027683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 499601614725993466814309 93675302761123775027683)
                  ·
                    rfl

theorem cell20_205236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_205236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205236 prefixEnd_205236 := by exact prefixLift 205236
  have htrace : WordTrace (prefixWord ++ tailWord_205236) baseStart_205236 baseEnd_205236 := by
    simpa [prefixWord, tailWord_205236, baseEnd_205236] using wordTrace_append hprefix tailTrace_205236
  have hstable : (prefixWord ++ tailWord_205236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205236).length < 2 ^ (prefixWord ++ tailWord_205236).sum := by decide
  have hdescent : baseEnd_205236 < baseStart_205236 := by decide
  rcases family_descends (prefixWord ++ tailWord_205236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205265 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_205265 : Nat := 118140960795 + 205265 * 2 ^ 59
def prefixEnd_205265 : Nat := 4983230072969 + 3 ^ 40 * 205265 * 2
def baseEnd_205265 : Nat := 93688539151328563060897

theorem tailTrace_205265 : CollatzResearch.WordTrace tailWord_205265 prefixEnd_205265 93688539151328563060897 := by
  unfold tailWord_205265
  simp only [CollatzResearch.WordTrace]
  refine ⟨7486629601367436316121249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4991086400911624210747499 7486629601367436316121249)
  ·
    refine ⟨5614972201025577237090937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7486629601367436316121249 5614972201025577237090937)
    ·
      refine ⟨4211229150769182927818203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5614972201025577237090937 4211229150769182927818203)
      ·
        refine ⟨6316843726153774391727305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4211229150769182927818203 6316843726153774391727305)
        ·
          refine ⟨4737632794615330793795479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6316843726153774391727305 4737632794615330793795479)
          ·
            refine ⟨7106449191922996190693219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4737632794615330793795479 7106449191922996190693219)
            ·
              refine ⟨10659673787884494286039829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106449191922996190693219 10659673787884494286039829)
              ·
                refine ⟨499672208807085669658117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10659673787884494286039829 499672208807085669658117)
                ·
                  refine ⟨93688539151328563060897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 499672208807085669658117 93688539151328563060897)
                  ·
                    rfl

theorem cell20_205265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_205265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205265 prefixEnd_205265 := by exact prefixLift 205265
  have htrace : WordTrace (prefixWord ++ tailWord_205265) baseStart_205265 baseEnd_205265 := by
    simpa [prefixWord, tailWord_205265, baseEnd_205265] using wordTrace_append hprefix tailTrace_205265
  have hstable : (prefixWord ++ tailWord_205265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205265).length < 2 ^ (prefixWord ++ tailWord_205265).sum := by decide
  have hdescent : baseEnd_205265 < baseStart_205265 := by decide
  rcases family_descends (prefixWord ++ tailWord_205265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205313 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 3]
def baseStart_205313 : Nat := 118140960795 + 205313 * 2 ^ 59
def prefixEnd_205313 : Nat := 4983230072969 + 3 ^ 40 * 205313 * 2
def baseEnd_205313 : Nat := 93710447659253729460701

theorem tailTrace_205313 : CollatzResearch.WordTrace tailWord_205313 prefixEnd_205313 93710447659253729460701 := by
  unfold tailWord_205313
  simp only [CollatzResearch.WordTrace]
  refine ⟨7488380305193540513868593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4992253536795693675912395 7488380305193540513868593)
  ·
    refine ⟨5616285228895155385401445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7488380305193540513868593 5616285228895155385401445)
    ·
      refine ⟨1053053480417841634762771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5616285228895155385401445 1053053480417841634762771)
      ·
        refine ⟨1579580220626762452144157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053053480417841634762771 1579580220626762452144157)
        ·
          refine ⟨592342582735035919554059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1579580220626762452144157 592342582735035919554059)
          ·
            refine ⟨888513874102553879331089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592342582735035919554059 888513874102553879331089)
            ·
              refine ⟨666385405576915409498317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888513874102553879331089 666385405576915409498317)
              ·
                refine ⟨249894527091343278561869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666385405576915409498317 249894527091343278561869)
                ·
                  refine ⟨93710447659253729460701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249894527091343278561869 93710447659253729460701)
                  ·
                    rfl

theorem cell20_205313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_205313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205313 prefixEnd_205313 := by exact prefixLift 205313
  have htrace : WordTrace (prefixWord ++ tailWord_205313) baseStart_205313 baseEnd_205313 := by
    simpa [prefixWord, tailWord_205313, baseEnd_205313] using wordTrace_append hprefix tailTrace_205313
  have hstable : (prefixWord ++ tailWord_205313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205313).length < 2 ^ (prefixWord ++ tailWord_205313).sum := by decide
  have hdescent : baseEnd_205313 < baseStart_205313 := by decide
  rcases family_descends (prefixWord ++ tailWord_205313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205364 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 3]
def baseStart_205364 : Nat := 118140960795 + 205364 * 2 ^ 59
def prefixEnd_205364 : Nat := 4983230072969 + 3 ^ 40 * 205364 * 2
def baseEnd_205364 : Nat := 93733725448924218760493

theorem tailTrace_205364 : CollatzResearch.WordTrace tailWord_205364 prefixEnd_205364 93733725448924218760493 := by
  unfold tailWord_205364
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745120214004388111987573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4993493618672517482650097 3745120214004388111987573)
  ·
    refine ⟨351105020062911385498835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3745120214004388111987573 351105020062911385498835)
    ·
      refine ⟨526657530094367078248253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351105020062911385498835 526657530094367078248253)
      ·
        refine ⟨197496573785387654343095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526657530094367078248253 197496573785387654343095)
        ·
          refine ⟨296244860678081481514643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197496573785387654343095 296244860678081481514643)
          ·
            refine ⟨444367291017122222271965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296244860678081481514643 444367291017122222271965)
            ·
              refine ⟨166637734131420833351987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 444367291017122222271965 166637734131420833351987)
              ·
                refine ⟨249956601197131250027981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166637734131420833351987 249956601197131250027981)
                ·
                  refine ⟨93733725448924218760493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249956601197131250027981 93733725448924218760493)
                  ·
                    rfl

theorem cell20_205364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_205364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205364 prefixEnd_205364 := by exact prefixLift 205364
  have htrace : WordTrace (prefixWord ++ tailWord_205364) baseStart_205364 baseEnd_205364 := by
    simpa [prefixWord, tailWord_205364, baseEnd_205364] using wordTrace_append hprefix tailTrace_205364
  have hstable : (prefixWord ++ tailWord_205364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205364).length < 2 ^ (prefixWord ++ tailWord_205364).sum := by decide
  have hdescent : baseEnd_205364 < baseStart_205364 := by decide
  rcases family_descends (prefixWord ++ tailWord_205364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205389 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 5]
def baseStart_205389 : Nat := 118140960795 + 205389 * 2 ^ 59
def prefixEnd_205389 : Nat := 4983230072969 + 3 ^ 40 * 205389 * 2
def baseEnd_205389 : Nat := 93745136130135242927057

theorem tailTrace_205389 : CollatzResearch.WordTrace tailWord_205389 prefixEnd_205389 93745136130135242927057 := by
  unfold tailWord_205389
  simp only [CollatzResearch.WordTrace]
  refine ⟨7491152252918205493635221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4994101501945470329090147 7491152252918205493635221)
  ·
    refine ⟨351147761855540882514151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7491152252918205493635221 351147761855540882514151)
    ·
      refine ⟨526721642783311323771227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351147761855540882514151 526721642783311323771227)
      ·
        refine ⟨790082464174966985656841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526721642783311323771227 790082464174966985656841)
        ·
          refine ⟨592561848131225239242631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790082464174966985656841 592561848131225239242631)
          ·
            refine ⟨888842772196837858863947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592561848131225239242631 888842772196837858863947)
            ·
              refine ⟨1333264158295256788295921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888842772196837858863947 1333264158295256788295921)
              ·
                refine ⟨999948118721442591221941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333264158295256788295921 999948118721442591221941)
                ·
                  refine ⟨93745136130135242927057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 999948118721442591221941 93745136130135242927057)
                  ·
                    rfl

theorem cell20_205389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_205389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205389 prefixEnd_205389 := by exact prefixLift 205389
  have htrace : WordTrace (prefixWord ++ tailWord_205389) baseStart_205389 baseEnd_205389 := by
    simpa [prefixWord, tailWord_205389, baseEnd_205389] using wordTrace_append hprefix tailTrace_205389
  have hstable : (prefixWord ++ tailWord_205389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205389).length < 2 ^ (prefixWord ++ tailWord_205389).sum := by decide
  have hdescent : baseEnd_205389 < baseStart_205389 := by decide
  rcases family_descends (prefixWord ++ tailWord_205389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205413 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 4]
def baseStart_205413 : Nat := 118140960795 + 205413 * 2 ^ 59
def prefixEnd_205413 : Nat := 4983230072969 + 3 ^ 40 * 205413 * 2
def baseEnd_205413 : Nat := 93756090384097826126959

theorem tailTrace_205413 : CollatzResearch.WordTrace tailWord_205413 prefixEnd_205413 93756090384097826126959 := by
  unfold tailWord_205413
  simp only [CollatzResearch.WordTrace]
  refine ⟨7492027604831257592508893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4994685069887505061672595 7492027604831257592508893)
  ·
    refine ⟨2809510351811721597190835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7492027604831257592508893 2809510351811721597190835)
    ·
      refine ⟨4214265527717582395786253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2809510351811721597190835 4214265527717582395786253)
      ·
        refine ⟨1580349572894093398419845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4214265527717582395786253 1580349572894093398419845)
        ·
          refine ⟨296315544917642512203721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1580349572894093398419845 296315544917642512203721)
          ·
            refine ⟨222236658688231884152791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296315544917642512203721 222236658688231884152791)
            ·
              refine ⟨333354988032347826229187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222236658688231884152791 333354988032347826229187)
              ·
                refine ⟨500032482048521739343781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333354988032347826229187 500032482048521739343781)
                ·
                  refine ⟨93756090384097826126959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 500032482048521739343781 93756090384097826126959)
                  ·
                    rfl

theorem cell20_205413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_205413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205413 prefixEnd_205413 := by exact prefixLift 205413
  have htrace : WordTrace (prefixWord ++ tailWord_205413) baseStart_205413 baseEnd_205413 := by
    simpa [prefixWord, tailWord_205413, baseEnd_205413] using wordTrace_append hprefix tailTrace_205413
  have hstable : (prefixWord ++ tailWord_205413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205413).length < 2 ^ (prefixWord ++ tailWord_205413).sum := by decide
  have hdescent : baseEnd_205413 < baseStart_205413 := by decide
  rcases family_descends (prefixWord ++ tailWord_205413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205468 : List Nat := [2, 2, 3, 2, 2, 1, 4, 2, 2]
def baseStart_205468 : Nat := 118140960795 + 205468 * 2 ^ 59
def prefixEnd_205468 : Nat := 4983230072969 + 3 ^ 40 * 205468 * 2
def baseEnd_205468 : Nat := 93781193882762079293401

theorem tailTrace_205468 : CollatzResearch.WordTrace tailWord_205468 prefixEnd_205468 93781193882762079293401 := by
  unfold tailWord_205468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3747016809816000992880529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4996022413088001323840705 3747016809816000992880529)
  ·
    refine ⟨2810262607362000744660397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3747016809816000992880529 2810262607362000744660397)
    ·
      refine ⟨1053848477760750279247649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2810262607362000744660397 1053848477760750279247649)
      ·
        refine ⟨790386358320562709435737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1053848477760750279247649 790386358320562709435737)
        ·
          refine ⟨592789768740422032076803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790386358320562709435737 592789768740422032076803)
          ·
            refine ⟨889184653110633048115205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592789768740422032076803 889184653110633048115205)
            ·
              refine ⟨166722122458243696521601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 889184653110633048115205 166722122458243696521601)
              ·
                refine ⟨125041591843682772391201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166722122458243696521601 125041591843682772391201)
                ·
                  refine ⟨93781193882762079293401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125041591843682772391201 93781193882762079293401)
                  ·
                    rfl

theorem cell20_205468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_205468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205468 prefixEnd_205468 := by exact prefixLift 205468
  have htrace : WordTrace (prefixWord ++ tailWord_205468) baseStart_205468 baseEnd_205468 := by
    simpa [prefixWord, tailWord_205468, baseEnd_205468] using wordTrace_append hprefix tailTrace_205468
  have hstable : (prefixWord ++ tailWord_205468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205468).length < 2 ^ (prefixWord ++ tailWord_205468).sum := by decide
  have hdescent : baseEnd_205468 < baseStart_205468 := by decide
  rcases family_descends (prefixWord ++ tailWord_205468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205489 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 4]
def baseStart_205489 : Nat := 118140960795 + 205489 * 2 ^ 59
def prefixEnd_205489 : Nat := 4983230072969 + 3 ^ 40 * 205489 * 2
def baseEnd_205489 : Nat := 93790778854979339593315

theorem tailTrace_205489 : CollatzResearch.WordTrace tailWord_205489 prefixEnd_205489 93790778854979339593315 := by
  unfold tailWord_205489
  simp only [CollatzResearch.WordTrace]
  refine ⟨7494799552555922572275521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4996533035037281714850347 7494799552555922572275521)
  ·
    refine ⟨5621099664416941929206641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7494799552555922572275521 5621099664416941929206641)
    ·
      refine ⟨4215824748312706446904981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5621099664416941929206641 4215824748312706446904981)
      ·
        refine ⟨197616785077158114698671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4215824748312706446904981 197616785077158114698671)
        ·
          refine ⟨296425177615737172048007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197616785077158114698671 296425177615737172048007)
          ·
            refine ⟨444637766423605758072011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296425177615737172048007 444637766423605758072011)
            ·
              refine ⟨666956649635408637108017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444637766423605758072011 666956649635408637108017)
              ·
                refine ⟨500217487226556477831013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666956649635408637108017 500217487226556477831013)
                ·
                  refine ⟨93790778854979339593315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 500217487226556477831013 93790778854979339593315)
                  ·
                    rfl

theorem cell20_205489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_205489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205489 prefixEnd_205489 := by exact prefixLift 205489
  have htrace : WordTrace (prefixWord ++ tailWord_205489) baseStart_205489 baseEnd_205489 := by
    simpa [prefixWord, tailWord_205489, baseEnd_205489] using wordTrace_append hprefix tailTrace_205489
  have hstable : (prefixWord ++ tailWord_205489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205489).length < 2 ^ (prefixWord ++ tailWord_205489).sum := by decide
  have hdescent : baseEnd_205489 < baseStart_205489 := by decide
  rcases family_descends (prefixWord ++ tailWord_205489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205557 : List Nat := [1, 3, 6, 1, 2, 1, 1, 3, 2]
def baseStart_205557 : Nat := 118140960795 + 205557 * 2 ^ 59
def prefixEnd_205557 : Nat := 4983230072969 + 3 ^ 40 * 205557 * 2
def baseEnd_205557 : Nat := 93821815907873325326371

theorem tailTrace_205557 : CollatzResearch.WordTrace tailWord_205557 prefixEnd_205557 93821815907873325326371 := by
  unfold tailWord_205557
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497279716309570185750925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4998186477539713457167283 7497279716309570185750925)
  ·
    refine ⟨2811479893616088819656597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7497279716309570185750925 2811479893616088819656597)
    ·
      refine ⟨131788120013254163421403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2811479893616088819656597 131788120013254163421403)
      ·
        refine ⟨197682180019881245132105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131788120013254163421403 197682180019881245132105)
        ·
          refine ⟨148261635014910933849079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197682180019881245132105 148261635014910933849079)
          ·
            refine ⟨222392452522366400773619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148261635014910933849079 222392452522366400773619)
            ·
              refine ⟨333588678783549601160429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222392452522366400773619 333588678783549601160429)
              ·
                refine ⟨125095754543831100435161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333588678783549601160429 125095754543831100435161)
                ·
                  refine ⟨93821815907873325326371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125095754543831100435161 93821815907873325326371)
                  ·
                    rfl

theorem cell20_205557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_205557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205557 prefixEnd_205557 := by exact prefixLift 205557
  have htrace : WordTrace (prefixWord ++ tailWord_205557) baseStart_205557 baseEnd_205557 := by
    simpa [prefixWord, tailWord_205557, baseEnd_205557] using wordTrace_append hprefix tailTrace_205557
  have hstable : (prefixWord ++ tailWord_205557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205557).length < 2 ^ (prefixWord ++ tailWord_205557).sum := by decide
  have hdescent : baseEnd_205557 < baseStart_205557 := by decide
  rcases family_descends (prefixWord ++ tailWord_205557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205576 : List Nat := [2, 1, 3, 2, 2, 2, 8]
def baseStart_205576 : Nat := 118140960795 + 205576 * 2 ^ 59
def prefixEnd_205576 : Nat := 4983230072969 + 3 ^ 40 * 205576 * 2
def baseEnd_205576 : Nat := 10425609780621522632551

theorem tailTrace_205576 : CollatzResearch.WordTrace tailWord_205576 prefixEnd_205576 10425609780621522632551 := by
  unfold tailWord_205576
  simp only [CollatzResearch.WordTrace]
  refine ⟨3748986351620368215346291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4998648468827157620461721 3748986351620368215346291)
  ·
    refine ⟨5623479527430552323019437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3748986351620368215346291 5623479527430552323019437)
    ·
      refine ⟨2108804822786457121132289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5623479527430552323019437 2108804822786457121132289)
      ·
        refine ⟨1581603617089842840849217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2108804822786457121132289 1581603617089842840849217)
        ·
          refine ⟨1186202712817382130636913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581603617089842840849217 1186202712817382130636913)
          ·
            refine ⟨889652034613036597977685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1186202712817382130636913 889652034613036597977685)
            ·
              refine ⟨10425609780621522632551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 889652034613036597977685 10425609780621522632551)
              ·
                rfl

theorem cell20_205576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 8].length) (baseStart_205576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205576 prefixEnd_205576 := by exact prefixLift 205576
  have htrace : WordTrace (prefixWord ++ tailWord_205576) baseStart_205576 baseEnd_205576 := by
    simpa [prefixWord, tailWord_205576, baseEnd_205576] using wordTrace_append hprefix tailTrace_205576
  have hstable : (prefixWord ++ tailWord_205576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205576).length < 2 ^ (prefixWord ++ tailWord_205576).sum := by decide
  have hdescent : baseEnd_205576 < baseStart_205576 := by decide
  rcases family_descends (prefixWord ++ tailWord_205576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205583 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_205583 : Nat := 118140960795 + 205583 * 2 ^ 59
def prefixEnd_205583 : Nat := 4983230072969 + 3 ^ 40 * 205583 * 2
def baseEnd_205583 : Nat := 93833683016332790459597

theorem tailTrace_205583 : CollatzResearch.WordTrace tailWord_205583 prefixEnd_205583 93833683016332790459597 := by
  unfold tailWord_205583
  simp only [CollatzResearch.WordTrace]
  refine ⟨7498228014215376626197403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4998818676143584417464935 7498228014215376626197403)
  ·
    refine ⟨11247342021323064939296105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7498228014215376626197403 11247342021323064939296105)
    ·
      refine ⟨8435506515992298704472079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11247342021323064939296105 8435506515992298704472079)
      ·
        refine ⟨12653259773988448056708119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8435506515992298704472079 12653259773988448056708119)
        ·
          refine ⟨18979889660982672085062179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12653259773988448056708119 18979889660982672085062179)
          ·
            refine ⟨28469834491474008127593269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18979889660982672085062179 28469834491474008127593269)
            ·
              refine ⟨2669046983575688261961869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28469834491474008127593269 2669046983575688261961869)
              ·
                refine ⟨1000892618840883098235701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2669046983575688261961869 1000892618840883098235701)
                ·
                  refine ⟨93833683016332790459597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1000892618840883098235701 93833683016332790459597)
                  ·
                    rfl

theorem cell20_205583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_205583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205583 prefixEnd_205583 := by exact prefixLift 205583
  have htrace : WordTrace (prefixWord ++ tailWord_205583) baseStart_205583 baseEnd_205583 := by
    simpa [prefixWord, tailWord_205583, baseEnd_205583] using wordTrace_append hprefix tailTrace_205583
  have hstable : (prefixWord ++ tailWord_205583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205583).length < 2 ^ (prefixWord ++ tailWord_205583).sum := by decide
  have hdescent : baseEnd_205583 < baseStart_205583 := by decide
  rcases family_descends (prefixWord ++ tailWord_205583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205596 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 3]
def baseStart_205596 : Nat := 118140960795 + 205596 * 2 ^ 59
def prefixEnd_205596 : Nat := 4983230072969 + 3 ^ 40 * 205596 * 2
def baseEnd_205596 : Nat := 93839616570562523026211

theorem tailTrace_205596 : CollatzResearch.WordTrace tailWord_205596 prefixEnd_205596 93839616570562523026211 := by
  unfold tailWord_205596
  simp only [CollatzResearch.WordTrace]
  refine ⟨3749351081584139923210321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4999134775445519897613761 3749351081584139923210321)
  ·
    refine ⟨2812013311188104942407741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3749351081584139923210321 2812013311188104942407741)
    ·
      refine ⟨1054504991695539353402903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2812013311188104942407741 1054504991695539353402903)
      ·
        refine ⟨1581757487543309030104355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054504991695539353402903 1581757487543309030104355)
        ·
          refine ⟨2372636231314963545156533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581757487543309030104355 2372636231314963545156533)
          ·
            refine ⟨222434646685777832358425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2372636231314963545156533 222434646685777832358425)
            ·
              refine ⟨166825985014333374268819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222434646685777832358425 166825985014333374268819)
              ·
                refine ⟨250238977521500061403229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166825985014333374268819 250238977521500061403229)
                ·
                  refine ⟨93839616570562523026211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250238977521500061403229 93839616570562523026211)
                  ·
                    rfl

theorem cell20_205596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_205596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205596 prefixEnd_205596 := by exact prefixLift 205596
  have htrace : WordTrace (prefixWord ++ tailWord_205596) baseStart_205596 baseEnd_205596 := by
    simpa [prefixWord, tailWord_205596, baseEnd_205596] using wordTrace_append hprefix tailTrace_205596
  have hstable : (prefixWord ++ tailWord_205596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205596).length < 2 ^ (prefixWord ++ tailWord_205596).sum := by decide
  have hdescent : baseEnd_205596 < baseStart_205596 := by decide
  rcases family_descends (prefixWord ++ tailWord_205596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205624 : List Nat := [2, 1, 2, 1, 3, 2, 2, 5, 2]
def baseStart_205624 : Nat := 118140960795 + 205624 * 2 ^ 59
def prefixEnd_205624 : Nat := 4983230072969 + 3 ^ 40 * 205624 * 2
def baseEnd_205624 : Nat := 93852396533518870092763

theorem tailTrace_205624 : CollatzResearch.WordTrace tailWord_205624 prefixEnd_205624 93852396533518870092763 := by
  unfold tailWord_205624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3749861703533420314219963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4999815604711227085626617 3749861703533420314219963)
  ·
    refine ⟨5624792555300130471329945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3749861703533420314219963 5624792555300130471329945)
    ·
      refine ⟨4218594416475097853497459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5624792555300130471329945 4218594416475097853497459)
      ·
        refine ⟨6327891624712646780246189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4218594416475097853497459 6327891624712646780246189)
        ·
          refine ⟨2372959359267242542592321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6327891624712646780246189 2372959359267242542592321)
          ·
            refine ⟨1779719519450431906944241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2372959359267242542592321 1779719519450431906944241)
            ·
              refine ⟨1334789639587823930208181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779719519450431906944241 1334789639587823930208181)
              ·
                refine ⟨125136528711358493457017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1334789639587823930208181 125136528711358493457017)
                ·
                  refine ⟨93852396533518870092763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125136528711358493457017 93852396533518870092763)
                  ·
                    rfl

theorem cell20_205624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_205624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205624 prefixEnd_205624 := by exact prefixLift 205624
  have htrace : WordTrace (prefixWord ++ tailWord_205624) baseStart_205624 baseEnd_205624 := by
    simpa [prefixWord, tailWord_205624, baseEnd_205624] using wordTrace_append hprefix tailTrace_205624
  have hstable : (prefixWord ++ tailWord_205624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205624).length < 2 ^ (prefixWord ++ tailWord_205624).sum := by decide
  have hdescent : baseEnd_205624 < baseStart_205624 := by decide
  rcases family_descends (prefixWord ++ tailWord_205624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205641 : List Nat := [1, 2, 1, 1, 2, 5, 4, 2, 2]
def baseStart_205641 : Nat := 118140960795 + 205641 * 2 ^ 59
def prefixEnd_205641 : Nat := 4983230072969 + 3 ^ 40 * 205641 * 2
def baseEnd_205641 : Nat := 93860155796742366526027

theorem tailTrace_205641 : CollatzResearch.WordTrace tailWord_205641 prefixEnd_205641 93860155796742366526027 := by
  unfold tailWord_205641
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500343448005252531808777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5000228965336835021205851 7500343448005252531808777)
  ·
    refine ⟨5625257586003939398856583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7500343448005252531808777 5625257586003939398856583)
    ·
      refine ⟨8437886379005909098284875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5625257586003939398856583 8437886379005909098284875)
      ·
        refine ⟨12656829568508863647427313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8437886379005909098284875 12656829568508863647427313)
        ·
          refine ⟨9492622176381647735570485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12656829568508863647427313 9492622176381647735570485)
          ·
            refine ⟨889933329035779475209733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9492622176381647735570485 889933329035779475209733)
            ·
              refine ⟨166862499194208651601825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 889933329035779475209733 166862499194208651601825)
              ·
                refine ⟨125146874395656488701369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166862499194208651601825 125146874395656488701369)
                ·
                  refine ⟨93860155796742366526027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125146874395656488701369 93860155796742366526027)
                  ·
                    rfl

theorem cell20_205641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_205641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205641 prefixEnd_205641 := by exact prefixLift 205641
  have htrace : WordTrace (prefixWord ++ tailWord_205641) baseStart_205641 baseEnd_205641 := by
    simpa [prefixWord, tailWord_205641, baseEnd_205641] using wordTrace_append hprefix tailTrace_205641
  have hstable : (prefixWord ++ tailWord_205641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205641).length < 2 ^ (prefixWord ++ tailWord_205641).sum := by decide
  have hdescent : baseEnd_205641 < baseStart_205641 := by decide
  rcases family_descends (prefixWord ++ tailWord_205641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205741 : List Nat := [1, 5, 2, 3, 2, 1, 6]
def baseStart_205741 : Nat := 118140960795 + 205741 * 2 ^ 59
def prefixEnd_205741 : Nat := 4983230072969 + 3 ^ 40 * 205741 * 2
def baseEnd_205741 : Nat := 10433977613509607021365

theorem tailTrace_205741 : CollatzResearch.WordTrace tailWord_205741 prefixEnd_205741 10433977613509607021365 := by
  unfold tailWord_205741
  simp only [CollatzResearch.WordTrace]
  refine ⟨7503990747642969610449077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5002660498428646406966051 7503990747642969610449077)
  ·
    refine ⟨703499132591528400979601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7503990747642969610449077 703499132591528400979601)
    ·
      refine ⟨527624349443646300734701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 703499132591528400979601 527624349443646300734701)
      ·
        refine ⟨197859131041367362775513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 527624349443646300734701 197859131041367362775513)
        ·
          refine ⟨148394348281025522081635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197859131041367362775513 148394348281025522081635)
          ·
            refine ⟨222591522421538283122453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148394348281025522081635 222591522421538283122453)
            ·
              refine ⟨10433977613509607021365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222591522421538283122453 10433977613509607021365)
              ·
                rfl

theorem cell20_205741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 6].length) (baseStart_205741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205741 prefixEnd_205741 := by exact prefixLift 205741
  have htrace : WordTrace (prefixWord ++ tailWord_205741) baseStart_205741 baseEnd_205741 := by
    simpa [prefixWord, tailWord_205741, baseEnd_205741] using wordTrace_append hprefix tailTrace_205741
  have hstable : (prefixWord ++ tailWord_205741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205741).length < 2 ^ (prefixWord ++ tailWord_205741).sum := by decide
  have hdescent : baseEnd_205741 < baseStart_205741 := by decide
  rcases family_descends (prefixWord ++ tailWord_205741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205745 : List Nat := [1, 2, 2, 4, 3, 2, 6]
def baseStart_205745 : Nat := 118140960795 + 205745 * 2 ^ 59
def prefixEnd_205745 : Nat := 4983230072969 + 3 ^ 40 * 205745 * 2
def baseEnd_205745 : Nat := 10434180470064469673215

theorem tailTrace_205745 : CollatzResearch.WordTrace tailWord_205745 prefixEnd_205745 10434180470064469673215 := by
  unfold tailWord_205745
  simp only [CollatzResearch.WordTrace]
  refine ⟨7504136639628478293594689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5002757759752318862396459 7504136639628478293594689)
  ·
    refine ⟨5628102479721358720196017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7504136639628478293594689 5628102479721358720196017)
    ·
      refine ⟨4221076859791019040147013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5628102479721358720196017 4221076859791019040147013)
      ·
        refine ⟨791451911210816070027565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4221076859791019040147013 791451911210816070027565)
        ·
          refine ⟨296794466704056026260337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 791451911210816070027565 296794466704056026260337)
          ·
            refine ⟨222595850028042019695253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296794466704056026260337 222595850028042019695253)
            ·
              refine ⟨10434180470064469673215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222595850028042019695253 10434180470064469673215)
              ·
                rfl

theorem cell20_205745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 6].length) (baseStart_205745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205745 prefixEnd_205745 := by exact prefixLift 205745
  have htrace : WordTrace (prefixWord ++ tailWord_205745) baseStart_205745 baseEnd_205745 := by
    simpa [prefixWord, tailWord_205745, baseEnd_205745] using wordTrace_append hprefix tailTrace_205745
  have hstable : (prefixWord ++ tailWord_205745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205745).length < 2 ^ (prefixWord ++ tailWord_205745).sum := by decide
  have hdescent : baseEnd_205745 < baseStart_205745 := by decide
  rcases family_descends (prefixWord ++ tailWord_205745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205810 : List Nat := [3, 2, 1, 5, 1, 1, 1, 4, 2]
def baseStart_205810 : Nat := 118140960795 + 205810 * 2 ^ 59
def prefixEnd_205810 : Nat := 4983230072969 + 3 ^ 40 * 205810 * 2
def baseEnd_205810 : Nat := 93937292001728889892003

theorem tailTrace_205810 : CollatzResearch.WordTrace tailWord_205810 prefixEnd_205810 93937292001728889892003 := by
  unfold tailWord_205810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876626846098248598677721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5004338256261996263140589 1876626846098248598677721)
  ·
    refine ⟨1407470134573686449008291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1876626846098248598677721 1407470134573686449008291)
    ·
      refine ⟨2111205201860529673512437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407470134573686449008291 2111205201860529673512437)
      ·
        refine ⟨197925487674424656891791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2111205201860529673512437 197925487674424656891791)
        ·
          refine ⟨296888231511636985337687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197925487674424656891791 296888231511636985337687)
          ·
            refine ⟨445332347267455478006531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296888231511636985337687 445332347267455478006531)
            ·
              refine ⟨667998520901183217009797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445332347267455478006531 667998520901183217009797)
              ·
                refine ⟨125249722668971853189337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 667998520901183217009797 125249722668971853189337)
                ·
                  refine ⟨93937292001728889892003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125249722668971853189337 93937292001728889892003)
                  ·
                    rfl

theorem cell20_205810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_205810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205810 prefixEnd_205810 := by exact prefixLift 205810
  have htrace : WordTrace (prefixWord ++ tailWord_205810) baseStart_205810 baseEnd_205810 := by
    simpa [prefixWord, tailWord_205810, baseEnd_205810] using wordTrace_append hprefix tailTrace_205810
  have hstable : (prefixWord ++ tailWord_205810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205810).length < 2 ^ (prefixWord ++ tailWord_205810).sum := by decide
  have hdescent : baseEnd_205810 < baseStart_205810 := by decide
  rcases family_descends (prefixWord ++ tailWord_205810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205818 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_205818 : Nat := 118140960795 + 205818 * 2 ^ 59
def prefixEnd_205818 : Nat := 4983230072969 + 3 ^ 40 * 205818 * 2
def baseEnd_205818 : Nat := 93940943419716417625303

theorem tailTrace_205818 : CollatzResearch.WordTrace tailWord_205818 prefixEnd_205818 93940943419716417625303 := by
  unfold tailWord_205818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876699792091002940250527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5004532778909341174001405 1876699792091002940250527)
  ·
    refine ⟨2815049688136504410375791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1876699792091002940250527 2815049688136504410375791)
    ·
      refine ⟨4222574532204756615563687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2815049688136504410375791 4222574532204756615563687)
      ·
        refine ⟨6333861798307134923345531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4222574532204756615563687 6333861798307134923345531)
        ·
          refine ⟨9500792697460702385018297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6333861798307134923345531 9500792697460702385018297)
          ·
            refine ⟨7125594523095526788763723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9500792697460702385018297 7125594523095526788763723)
            ·
              refine ⟨10688391784643290183145585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7125594523095526788763723 10688391784643290183145585)
              ·
                refine ⟨8016293838482467637359189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10688391784643290183145585 8016293838482467637359189)
                ·
                  refine ⟨93940943419716417625303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8016293838482467637359189 93940943419716417625303)
                  ·
                    rfl

theorem cell20_205818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_205818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205818 prefixEnd_205818 := by exact prefixLift 205818
  have htrace : WordTrace (prefixWord ++ tailWord_205818) baseStart_205818 baseEnd_205818 := by
    simpa [prefixWord, tailWord_205818, baseEnd_205818] using wordTrace_append hprefix tailTrace_205818
  have hstable : (prefixWord ++ tailWord_205818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205818).length < 2 ^ (prefixWord ++ tailWord_205818).sum := by decide
  have hdescent : baseEnd_205818 < baseStart_205818 := by decide
  rcases family_descends (prefixWord ++ tailWord_205818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205835 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 4]
def baseStart_205835 : Nat := 118140960795 + 205835 * 2 ^ 59
def prefixEnd_205835 : Nat := 4983230072969 + 3 ^ 40 * 205835 * 2
def baseEnd_205835 : Nat := 93948702682939914058567

theorem tailTrace_205835 : CollatzResearch.WordTrace tailWord_205835 prefixEnd_205835 93948702682939914058567 := by
  unfold tailWord_205835
  simp only [CollatzResearch.WordTrace]
  refine ⟨7507419209302423664370959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5004946139534949109580639 7507419209302423664370959)
  ·
    refine ⟨11261128813953635496556439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7507419209302423664370959 11261128813953635496556439)
    ·
      refine ⟨16891693220930453244834659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11261128813953635496556439 16891693220930453244834659)
      ·
        refine ⟨25337539831395679867251989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16891693220930453244834659 25337539831395679867251989)
        ·
          refine ⟨1187697179596672493777437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25337539831395679867251989 1187697179596672493777437)
          ·
            refine ⟨445386442348752185166539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1187697179596672493777437 445386442348752185166539)
            ·
              refine ⟨668079663523128277749809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445386442348752185166539 668079663523128277749809)
              ·
                refine ⟨501059747642346208312357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668079663523128277749809 501059747642346208312357)
                ·
                  refine ⟨93948702682939914058567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 501059747642346208312357 93948702682939914058567)
                  ·
                    rfl

theorem cell20_205835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_205835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205835 prefixEnd_205835 := by exact prefixLift 205835
  have htrace : WordTrace (prefixWord ++ tailWord_205835) baseStart_205835 baseEnd_205835 := by
    simpa [prefixWord, tailWord_205835, baseEnd_205835] using wordTrace_append hprefix tailTrace_205835
  have hstable : (prefixWord ++ tailWord_205835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205835).length < 2 ^ (prefixWord ++ tailWord_205835).sum := by decide
  have hdescent : baseEnd_205835 < baseStart_205835 := by decide
  rcases family_descends (prefixWord ++ tailWord_205835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205873 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 4]
def baseStart_205873 : Nat := 118140960795 + 205873 * 2 ^ 59
def prefixEnd_205873 : Nat := 4983230072969 + 3 ^ 40 * 205873 * 2
def baseEnd_205873 : Nat := 93966046918380670791745

theorem tailTrace_205873 : CollatzResearch.WordTrace tailWord_205873 prefixEnd_205873 93966046918380670791745 := by
  unfold tailWord_205873
  simp only [CollatzResearch.WordTrace]
  refine ⟨7508805183164756154254273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5005870122109837436169515 7508805183164756154254273)
  ·
    refine ⟨5631603887373567115690705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7508805183164756154254273 5631603887373567115690705)
    ·
      refine ⟨4223702915530175336768029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5631603887373567115690705 4223702915530175336768029)
      ·
        refine ⟨1583888593323815751288011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4223702915530175336768029 1583888593323815751288011)
        ·
          refine ⟨2375832889985723626932017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583888593323815751288011 2375832889985723626932017)
          ·
            refine ⟨1781874667489292720199013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375832889985723626932017 1781874667489292720199013)
            ·
              refine ⟨334101500154242385037315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1781874667489292720199013 334101500154242385037315)
              ·
                refine ⟨501152250231363577555973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334101500154242385037315 501152250231363577555973)
                ·
                  refine ⟨93966046918380670791745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 501152250231363577555973 93966046918380670791745)
                  ·
                    rfl

theorem cell20_205873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_205873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205873 prefixEnd_205873 := by exact prefixLift 205873
  have htrace : WordTrace (prefixWord ++ tailWord_205873) baseStart_205873 baseEnd_205873 := by
    simpa [prefixWord, tailWord_205873, baseEnd_205873] using wordTrace_append hprefix tailTrace_205873
  have hstable : (prefixWord ++ tailWord_205873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205873).length < 2 ^ (prefixWord ++ tailWord_205873).sum := by decide
  have hdescent : baseEnd_205873 < baseStart_205873 := by decide
  rcases family_descends (prefixWord ++ tailWord_205873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205925 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_205925 : Nat := 118140960795 + 205925 * 2 ^ 59
def prefixEnd_205925 : Nat := 4983230072969 + 3 ^ 40 * 205925 * 2
def baseEnd_205925 : Nat := 93989781135299601058199

theorem tailTrace_205925 : CollatzResearch.WordTrace tailWord_205925 prefixEnd_205925 93989781135299601058199 := by
  unfold tailWord_205925
  simp only [CollatzResearch.WordTrace]
  refine ⟨7510701778976369035147229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5007134519317579356764819 7510701778976369035147229)
  ·
    refine ⟨2816513167116138388180211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7510701778976369035147229 2816513167116138388180211)
    ·
      refine ⟨4224769750674207582270317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816513167116138388180211 4224769750674207582270317)
      ·
        refine ⟨1584288656502827843351369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4224769750674207582270317 1584288656502827843351369)
        ·
          refine ⟨1188216492377120882513527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1584288656502827843351369 1188216492377120882513527)
          ·
            refine ⟨1782324738565681323770291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188216492377120882513527 1782324738565681323770291)
            ·
              refine ⟨2673487107848521985655437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782324738565681323770291 2673487107848521985655437)
              ·
                refine ⟨1002557665443195744620789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2673487107848521985655437 1002557665443195744620789)
                ·
                  refine ⟨93989781135299601058199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1002557665443195744620789 93989781135299601058199)
                  ·
                    rfl

theorem cell20_205925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_205925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205925 prefixEnd_205925 := by exact prefixLift 205925
  have htrace : WordTrace (prefixWord ++ tailWord_205925) baseStart_205925 baseEnd_205925 := by
    simpa [prefixWord, tailWord_205925, baseEnd_205925] using wordTrace_append hprefix tailTrace_205925
  have hstable : (prefixWord ++ tailWord_205925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205925).length < 2 ^ (prefixWord ++ tailWord_205925).sum := by decide
  have hdescent : baseEnd_205925 < baseStart_205925 := by decide
  rcases family_descends (prefixWord ++ tailWord_205925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205956 : List Nat := [2, 3, 2, 1, 2, 2, 2, 6]
def baseStart_205956 : Nat := 118140960795 + 205956 * 2 ^ 59
def prefixEnd_205956 : Nat := 4983230072969 + 3 ^ 40 * 205956 * 2
def baseEnd_205956 : Nat := 31334643460000423674913

theorem tailTrace_205956 : CollatzResearch.WordTrace tailWord_205956 prefixEnd_205956 31334643460000423674913 := by
  unfold tailWord_205956
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755916220932030664762861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5007888294576040886350481 3755916220932030664762861)
  ·
    refine ⟨1408468582849511499286073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3755916220932030664762861 1408468582849511499286073)
    ·
      refine ⟨1056351437137133624464555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1408468582849511499286073 1056351437137133624464555)
      ·
        refine ⟨1584527155705700436696833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056351437137133624464555 1584527155705700436696833)
        ·
          refine ⟨1188395366779275327522625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1584527155705700436696833 1188395366779275327522625)
          ·
            refine ⟨891296525084456495641969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188395366779275327522625 891296525084456495641969)
            ·
              refine ⟨668472393813342371731477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891296525084456495641969 668472393813342371731477)
              ·
                refine ⟨31334643460000423674913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 668472393813342371731477 31334643460000423674913)
                ·
                  rfl

theorem cell20_205956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_205956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205956 prefixEnd_205956 := by exact prefixLift 205956
  have htrace : WordTrace (prefixWord ++ tailWord_205956) baseStart_205956 baseEnd_205956 := by
    simpa [prefixWord, tailWord_205956, baseEnd_205956] using wordTrace_append hprefix tailTrace_205956
  have hstable : (prefixWord ++ tailWord_205956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205956).length < 2 ^ (prefixWord ++ tailWord_205956).sum := by decide
  have hdescent : baseEnd_205956 < baseStart_205956 := by decide
  rcases family_descends (prefixWord ++ tailWord_205956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205980 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 3]
def baseStart_205980 : Nat := 118140960795 + 205980 * 2 ^ 59
def prefixEnd_205980 : Nat := 4983230072969 + 3 ^ 40 * 205980 * 2
def baseEnd_205980 : Nat := 94014884633963854224641

theorem tailTrace_205980 : CollatzResearch.WordTrace tailWord_205980 prefixEnd_205980 94014884633963854224641 := by
  unfold tailWord_205980
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756353896888556714199697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5008471862518075618932929 3756353896888556714199697)
  ·
    refine ⟨2817265422666417535649773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3756353896888556714199697 2817265422666417535649773)
    ·
      refine ⟨1056474533499906575868665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2817265422666417535649773 1056474533499906575868665)
      ·
        refine ⟨792355900124929931901499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1056474533499906575868665 792355900124929931901499)
        ·
          refine ⟨1188533850187394897852249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792355900124929931901499 1188533850187394897852249)
          ·
            refine ⟨891400387640546173389187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188533850187394897852249 891400387640546173389187)
            ·
              refine ⟨1337100581460819260083781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891400387640546173389187 1337100581460819260083781)
              ·
                refine ⟨250706359023903611265709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1337100581460819260083781 250706359023903611265709)
                ·
                  refine ⟨94014884633963854224641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250706359023903611265709 94014884633963854224641)
                  ·
                    rfl

theorem cell20_205980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_205980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205980 prefixEnd_205980 := by exact prefixLift 205980
  have htrace : WordTrace (prefixWord ++ tailWord_205980) baseStart_205980 baseEnd_205980 := by
    simpa [prefixWord, tailWord_205980, baseEnd_205980] using wordTrace_append hprefix tailTrace_205980
  have hstable : (prefixWord ++ tailWord_205980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205980).length < 2 ^ (prefixWord ++ tailWord_205980).sum := by decide
  have hdescent : baseEnd_205980 < baseStart_205980 := by decide
  rcases family_descends (prefixWord ++ tailWord_205980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205983 : List Nat := [1, 1, 2, 6, 2, 1, 1, 4, 2]
def baseStart_205983 : Nat := 118140960795 + 205983 * 2 ^ 59
def prefixEnd_205983 : Nat := 4983230072969 + 3 ^ 40 * 205983 * 2
def baseEnd_205983 : Nat := 94016253915709177124629

theorem tailTrace_205983 : CollatzResearch.WordTrace tailWord_205983 prefixEnd_205983 94016253915709177124629 := by
  unfold tailWord_205983
  simp only [CollatzResearch.WordTrace]
  refine ⟨7512817212766244940758603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5008544808510829960505735 7512817212766244940758603)
  ·
    refine ⟨11269225819149367411137905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7512817212766244940758603 11269225819149367411137905)
    ·
      refine ⟨8451919364362025558353429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11269225819149367411137905 8451919364362025558353429)
      ·
        refine ⟨396183720204469948047817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8451919364362025558353429 396183720204469948047817)
        ·
          refine ⟨297137790153352461035863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396183720204469948047817 297137790153352461035863)
          ·
            refine ⟨445706685230028691553795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297137790153352461035863 445706685230028691553795)
            ·
              refine ⟨668560027845043037330693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445706685230028691553795 668560027845043037330693)
              ·
                refine ⟨125355005220945569499505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 668560027845043037330693 125355005220945569499505)
                ·
                  refine ⟨94016253915709177124629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125355005220945569499505 94016253915709177124629)
                  ·
                    rfl

theorem cell20_205983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 2].length) (baseStart_205983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_205983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_205983 prefixEnd_205983 := by exact prefixLift 205983
  have htrace : WordTrace (prefixWord ++ tailWord_205983) baseStart_205983 baseEnd_205983 := by
    simpa [prefixWord, tailWord_205983, baseEnd_205983] using wordTrace_append hprefix tailTrace_205983
  have hstable : (prefixWord ++ tailWord_205983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205983).length < 2 ^ (prefixWord ++ tailWord_205983).sum := by decide
  have hdescent : baseEnd_205983 < baseStart_205983 := by decide
  rcases family_descends (prefixWord ++ tailWord_205983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206015 : List Nat := [1, 1, 2, 2, 2, 2, 2, 8]
def baseStart_206015 : Nat := 118140960795 + 206015 * 2 ^ 59
def prefixEnd_206015 : Nat := 4983230072969 + 3 ^ 40 * 206015 * 2
def baseEnd_206015 : Nat := 31343619862553096019277

theorem tailTrace_206015 : CollatzResearch.WordTrace tailWord_206015 prefixEnd_206015 31343619862553096019277 := by
  unfold tailWord_206015
  simp only [CollatzResearch.WordTrace]
  refine ⟨7513984348650314405923499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5009322899100209603948999 7513984348650314405923499)
  ·
    refine ⟨11270976522975471608885249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7513984348650314405923499 11270976522975471608885249)
    ·
      refine ⟨8453232392231603706663937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11270976522975471608885249 8453232392231603706663937)
      ·
        refine ⟨6339924294173702779997953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8453232392231603706663937 6339924294173702779997953)
        ·
          refine ⟨4754943220630277084998465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6339924294173702779997953 4754943220630277084998465)
          ·
            refine ⟨3566207415472707813748849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4754943220630277084998465 3566207415472707813748849)
            ·
              refine ⟨2674655561604530860311637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3566207415472707813748849 2674655561604530860311637)
              ·
                refine ⟨31343619862553096019277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2674655561604530860311637 31343619862553096019277)
                ·
                  rfl

theorem cell20_206015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_206015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206015 prefixEnd_206015 := by exact prefixLift 206015
  have htrace : WordTrace (prefixWord ++ tailWord_206015) baseStart_206015 baseEnd_206015 := by
    simpa [prefixWord, tailWord_206015, baseEnd_206015] using wordTrace_append hprefix tailTrace_206015
  have hstable : (prefixWord ++ tailWord_206015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206015).length < 2 ^ (prefixWord ++ tailWord_206015).sum := by decide
  have hdescent : baseEnd_206015 < baseStart_206015 := by decide
  rcases family_descends (prefixWord ++ tailWord_206015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206066 : List Nat := [3, 2, 1, 3, 3, 2, 2, 4]
def baseStart_206066 : Nat := 118140960795 + 206066 * 2 ^ 59
def prefixEnd_206066 : Nat := 4983230072969 + 3 ^ 40 * 206066 * 2
def baseEnd_206066 : Nat := 31351379125776592452541

theorem tailTrace_206066 : CollatzResearch.WordTrace tailWord_206066 prefixEnd_206066 31351379125776592452541 := by
  unfold tailWord_206066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878961117866387529007513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5010562980977033410686701 1878961117866387529007513)
  ·
    refine ⟨1409220838399790646755635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1878961117866387529007513 1409220838399790646755635)
    ·
      refine ⟨2113831257599685970133453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1409220838399790646755635 2113831257599685970133453)
      ·
        refine ⟨792686721599882238800045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2113831257599685970133453 792686721599882238800045)
        ·
          refine ⟨297257520599955839550017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 792686721599882238800045 297257520599955839550017)
          ·
            refine ⟨222943140449966879662513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297257520599955839550017 222943140449966879662513)
            ·
              refine ⟨167207355337475159746885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222943140449966879662513 167207355337475159746885)
              ·
                refine ⟨31351379125776592452541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167207355337475159746885 31351379125776592452541)
                ·
                  rfl

theorem cell20_206066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_206066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206066 prefixEnd_206066 := by exact prefixLift 206066
  have htrace : WordTrace (prefixWord ++ tailWord_206066) baseStart_206066 baseEnd_206066 := by
    simpa [prefixWord, tailWord_206066, baseEnd_206066] using wordTrace_append hprefix tailTrace_206066
  have hstable : (prefixWord ++ tailWord_206066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206066).length < 2 ^ (prefixWord ++ tailWord_206066).sum := by decide
  have hdescent : baseEnd_206066 < baseStart_206066 := by decide
  rcases family_descends (prefixWord ++ tailWord_206066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206076 : List Nat := [2, 2, 2, 1, 6, 1, 1, 3, 2]
def baseStart_206076 : Nat := 118140960795 + 206076 * 2 ^ 59
def prefixEnd_206076 : Nat := 4983230072969 + 3 ^ 40 * 206076 * 2
def baseEnd_206076 : Nat := 94058701649814187024249

theorem tailTrace_206076 : CollatzResearch.WordTrace tailWord_206076 prefixEnd_206076 94058701649814187024249 := by
  unfold tailWord_206076
  simp only [CollatzResearch.WordTrace]
  refine ⟨3758104600714660911947041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5010806134286214549262721 3758104600714660911947041)
  ·
    refine ⟨2818578450535995683960281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3758104600714660911947041 2818578450535995683960281)
    ·
      refine ⟨2113933837901996762970211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2818578450535995683960281 2113933837901996762970211)
      ·
        refine ⟨3170900756852995144455317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113933837901996762970211 3170900756852995144455317)
        ·
          refine ⟨148635972977484147396343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3170900756852995144455317 148635972977484147396343)
          ·
            refine ⟨222953959466226221094515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148635972977484147396343 222953959466226221094515)
            ·
              refine ⟨334430939199339331641773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222953959466226221094515 334430939199339331641773)
              ·
                refine ⟨125411602199752249365665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334430939199339331641773 125411602199752249365665)
                ·
                  refine ⟨94058701649814187024249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125411602199752249365665 94058701649814187024249)
                  ·
                    rfl

theorem cell20_206076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_206076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206076 prefixEnd_206076 := by exact prefixLift 206076
  have htrace : WordTrace (prefixWord ++ tailWord_206076) baseStart_206076 baseEnd_206076 := by
    simpa [prefixWord, tailWord_206076, baseEnd_206076] using wordTrace_append hprefix tailTrace_206076
  have hstable : (prefixWord ++ tailWord_206076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206076).length < 2 ^ (prefixWord ++ tailWord_206076).sum := by decide
  have hdescent : baseEnd_206076 < baseStart_206076 := by decide
  rcases family_descends (prefixWord ++ tailWord_206076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206091 : List Nat := [1, 1, 1, 1, 5, 3, 8]
def baseStart_206091 : Nat := 118140960795 + 206091 * 2 ^ 59
def prefixEnd_206091 : Nat := 4983230072969 + 3 ^ 40 * 206091 * 2
def baseEnd_206091 : Nat := 10451727562060089058243

theorem tailTrace_206091 : CollatzResearch.WordTrace tailWord_206091 prefixEnd_206091 10451727562060089058243 := by
  unfold tailWord_206091
  simp only [CollatzResearch.WordTrace]
  refine ⟨7516756296374979385690127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5011170864249986257126751 7516756296374979385690127)
  ·
    refine ⟨11275134444562469078535191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7516756296374979385690127 11275134444562469078535191)
    ·
      refine ⟨16912701666843703617802787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11275134444562469078535191 16912701666843703617802787)
      ·
        refine ⟨25369052500265555426704181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16912701666843703617802787 25369052500265555426704181)
        ·
          refine ⟨2378348671899895821253517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25369052500265555426704181 2378348671899895821253517)
          ·
            refine ⟨891880751962460932970069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2378348671899895821253517 891880751962460932970069)
            ·
              refine ⟨10451727562060089058243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 891880751962460932970069 10451727562060089058243)
              ·
                rfl

theorem cell20_206091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 8].length) (baseStart_206091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206091 prefixEnd_206091 := by exact prefixLift 206091
  have htrace : WordTrace (prefixWord ++ tailWord_206091) baseStart_206091 baseEnd_206091 := by
    simpa [prefixWord, tailWord_206091, baseEnd_206091] using wordTrace_append hprefix tailTrace_206091
  have hstable : (prefixWord ++ tailWord_206091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206091).length < 2 ^ (prefixWord ++ tailWord_206091).sum := by decide
  have hdescent : baseEnd_206091 < baseStart_206091 := by decide
  rcases family_descends (prefixWord ++ tailWord_206091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206125 : List Nat := [1, 5, 3, 1, 1, 1, 2, 6]
def baseStart_206125 : Nat := 118140960795 + 206125 * 2 ^ 59
def prefixEnd_206125 : Nat := 4983230072969 + 3 ^ 40 * 206125 * 2
def baseEnd_206125 : Nat := 31360355528329264796905

theorem tailTrace_206125 : CollatzResearch.WordTrace tailWord_206125 prefixEnd_206125 31360355528329264796905 := by
  unfold tailWord_206125
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517996378251803192427829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5011997585501202128285219 7517996378251803192427829)
  ·
    refine ⟨704812160461106549290109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7517996378251803192427829 704812160461106549290109)
    ·
      refine ⟨264304560172914955983791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 704812160461106549290109 264304560172914955983791)
      ·
        refine ⟨396456840259372433975687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264304560172914955983791 396456840259372433975687)
        ·
          refine ⟨594685260389058650963531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396456840259372433975687 594685260389058650963531)
          ·
            refine ⟨892027890583587976445297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594685260389058650963531 892027890583587976445297)
            ·
              refine ⟨669020917937690982333973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892027890583587976445297 669020917937690982333973)
              ·
                refine ⟨31360355528329264796905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 669020917937690982333973 31360355528329264796905)
                ·
                  rfl

theorem cell20_206125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 6].length) (baseStart_206125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206125 prefixEnd_206125 := by exact prefixLift 206125
  have htrace : WordTrace (prefixWord ++ tailWord_206125) baseStart_206125 baseEnd_206125 := by
    simpa [prefixWord, tailWord_206125, baseEnd_206125] using wordTrace_append hprefix tailTrace_206125
  have hstable : (prefixWord ++ tailWord_206125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206125).length < 2 ^ (prefixWord ++ tailWord_206125).sum := by decide
  have hdescent : baseEnd_206125 < baseStart_206125 := by decide
  rcases family_descends (prefixWord ++ tailWord_206125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206153 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 3]
def baseStart_206153 : Nat := 118140960795 + 206153 * 2 ^ 59
def prefixEnd_206153 : Nat := 4983230072969 + 3 ^ 40 * 206153 * 2
def baseEnd_206153 : Nat := 94093846547944141457267

theorem tailTrace_206153 : CollatzResearch.WordTrace tailWord_206153 prefixEnd_206153 94093846547944141457267 := by
  unfold tailWord_206153
  simp only [CollatzResearch.WordTrace]
  refine ⟨7519017622150363974447113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5012678414766909316298075 7519017622150363974447113)
  ·
    refine ⟨5639263216612772980835335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7519017622150363974447113 5639263216612772980835335)
    ·
      refine ⟨8458894824919159471253003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5639263216612772980835335 8458894824919159471253003)
      ·
        refine ⟨12688342237378739206879505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8458894824919159471253003 12688342237378739206879505)
        ·
          refine ⟨9516256678034054405159629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12688342237378739206879505 9516256678034054405159629)
          ·
            refine ⟨3568596254262770401934861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9516256678034054405159629 3568596254262770401934861)
            ·
              refine ⟨1338223595348538900725573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3568596254262770401934861 1338223595348538900725573)
              ·
                refine ⟨250916924127851043886045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1338223595348538900725573 250916924127851043886045)
                ·
                  refine ⟨94093846547944141457267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250916924127851043886045 94093846547944141457267)
                  ·
                    rfl

theorem cell20_206153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_206153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206153 prefixEnd_206153 := by exact prefixLift 206153
  have htrace : WordTrace (prefixWord ++ tailWord_206153) baseStart_206153 baseEnd_206153 := by
    simpa [prefixWord, tailWord_206153, baseEnd_206153] using wordTrace_append hprefix tailTrace_206153
  have hstable : (prefixWord ++ tailWord_206153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206153).length < 2 ^ (prefixWord ++ tailWord_206153).sum := by decide
  have hdescent : baseEnd_206153 < baseStart_206153 := by decide
  rcases family_descends (prefixWord ++ tailWord_206153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206156 : List Nat := [2, 2, 1, 3, 2, 3, 1, 4, 2]
def baseStart_206156 : Nat := 118140960795 + 206156 * 2 ^ 59
def prefixEnd_206156 : Nat := 4983230072969 + 3 ^ 40 * 206156 * 2
def baseEnd_206156 : Nat := 94095215829689464357255

theorem tailTrace_206156 : CollatzResearch.WordTrace tailWord_206156 prefixEnd_206156 94095215829689464357255 := by
  unfold tailWord_206156
  simp only [CollatzResearch.WordTrace]
  refine ⟨3759563520569747743403161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5012751360759663657870881 3759563520569747743403161)
  ·
    refine ⟨2819672640427310807552371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3759563520569747743403161 2819672640427310807552371)
    ·
      refine ⟨4229508960640966211328557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2819672640427310807552371 4229508960640966211328557)
      ·
        refine ⟨1586065860240362329248209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4229508960640966211328557 1586065860240362329248209)
        ·
          refine ⟨1189549395180271746936157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586065860240362329248209 1189549395180271746936157)
          ·
            refine ⟨446081023192601905101059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1189549395180271746936157 446081023192601905101059)
            ·
              refine ⟨669121534788902857651589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446081023192601905101059 669121534788902857651589)
              ·
                refine ⟨125460287772919285809673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669121534788902857651589 125460287772919285809673)
                ·
                  refine ⟨94095215829689464357255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125460287772919285809673 94095215829689464357255)
                  ·
                    rfl

theorem cell20_206156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_206156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206156 prefixEnd_206156 := by exact prefixLift 206156
  have htrace : WordTrace (prefixWord ++ tailWord_206156) baseStart_206156 baseEnd_206156 := by
    simpa [prefixWord, tailWord_206156, baseEnd_206156] using wordTrace_append hprefix tailTrace_206156
  have hstable : (prefixWord ++ tailWord_206156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206156).length < 2 ^ (prefixWord ++ tailWord_206156).sum := by decide
  have hdescent : baseEnd_206156 < baseStart_206156 := by decide
  rcases family_descends (prefixWord ++ tailWord_206156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206160 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_206160 : Nat := 118140960795 + 206160 * 2 ^ 59
def prefixEnd_206160 : Nat := 4983230072969 + 3 ^ 40 * 206160 * 2
def baseEnd_206160 : Nat := 94097041538683228223905

theorem tailTrace_206160 : CollatzResearch.WordTrace tailWord_206160 prefixEnd_206160 94097041538683228223905 := by
  unfold tailWord_206160
  simp only [CollatzResearch.WordTrace]
  refine ⟨3759636466562502084975967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5012848622083336113301289 3759636466562502084975967)
  ·
    refine ⟨5639454699843753127463951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3759636466562502084975967 5639454699843753127463951)
    ·
      refine ⟨8459182049765629691195927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5639454699843753127463951 8459182049765629691195927)
      ·
        refine ⟨12688773074648444536793891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8459182049765629691195927 12688773074648444536793891)
        ·
          refine ⟨19033159611972666805190837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12688773074648444536793891 19033159611972666805190837)
          ·
            refine ⟨1784358713622437512986641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19033159611972666805190837 1784358713622437512986641)
            ·
              refine ⟨1338269035216828134739981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784358713622437512986641 1338269035216828134739981)
              ·
                refine ⟨501850888206310550527493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338269035216828134739981 501850888206310550527493)
                ·
                  refine ⟨94097041538683228223905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 501850888206310550527493 94097041538683228223905)
                  ·
                    rfl

theorem cell20_206160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_206160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206160 prefixEnd_206160 := by exact prefixLift 206160
  have htrace : WordTrace (prefixWord ++ tailWord_206160) baseStart_206160 baseEnd_206160 := by
    simpa [prefixWord, tailWord_206160, baseEnd_206160] using wordTrace_append hprefix tailTrace_206160
  have hstable : (prefixWord ++ tailWord_206160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206160).length < 2 ^ (prefixWord ++ tailWord_206160).sum := by decide
  have hdescent : baseEnd_206160 < baseStart_206160 := by decide
  rcases family_descends (prefixWord ++ tailWord_206160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206190 : List Nat := [4, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_206190 : Nat := 118140960795 + 206190 * 2 ^ 59
def prefixEnd_206190 : Nat := 4983230072969 + 3 ^ 40 * 206190 * 2
def baseEnd_206190 : Nat := 94110734356136457223783

theorem tailTrace_206190 : CollatzResearch.WordTrace tailWord_206190 prefixEnd_206190 94110734356136457223783 := by
  unfold tailWord_206190
  simp only [CollatzResearch.WordTrace]
  refine ⟨940045890377039911693003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5013578082010879529029349 940045890377039911693003)
  ·
    refine ⟨1410068835565559867539505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 940045890377039911693003 1410068835565559867539505)
    ·
      refine ⟨1057551626674169900654629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1410068835565559867539505 1057551626674169900654629)
      ·
        refine ⟨198290930001406856372743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1057551626674169900654629 198290930001406856372743)
        ·
          refine ⟨297436395002110284559115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198290930001406856372743 297436395002110284559115)
          ·
            refine ⟨446154592503165426838673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297436395002110284559115 446154592503165426838673)
            ·
              refine ⟨334615944377374070129005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446154592503165426838673 334615944377374070129005)
              ·
                refine ⟨125480979141515276298377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334615944377374070129005 125480979141515276298377)
                ·
                  refine ⟨94110734356136457223783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125480979141515276298377 94110734356136457223783)
                  ·
                    rfl

theorem cell20_206190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_206190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206190 prefixEnd_206190 := by exact prefixLift 206190
  have htrace : WordTrace (prefixWord ++ tailWord_206190) baseStart_206190 baseEnd_206190 := by
    simpa [prefixWord, tailWord_206190, baseEnd_206190] using wordTrace_append hprefix tailTrace_206190
  have hstable : (prefixWord ++ tailWord_206190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206190).length < 2 ^ (prefixWord ++ tailWord_206190).sum := by decide
  have hdescent : baseEnd_206190 < baseStart_206190 := by decide
  rcases family_descends (prefixWord ++ tailWord_206190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206194 : List Nat := [3, 2, 1, 2, 1, 2, 4, 3, 2]
def baseStart_206194 : Nat := 118140960795 + 206194 * 2 ^ 59
def prefixEnd_206194 : Nat := 4983230072969 + 3 ^ 40 * 206194 * 2
def baseEnd_206194 : Nat := 94112560065130221090433

theorem tailTrace_206194 : CollatzResearch.WordTrace tailWord_206194 prefixEnd_206194 94112560065130221090433 := by
  unfold tailWord_206194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1880128253750456994172409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5013675343334551984459757 1880128253750456994172409)
  ·
    refine ⟨1410096190312842745629307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1880128253750456994172409 1410096190312842745629307)
    ·
      refine ⟨2115144285469264118443961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410096190312842745629307 2115144285469264118443961)
      ·
        refine ⟨1586358214101948088832971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2115144285469264118443961 1586358214101948088832971)
        ·
          refine ⟨2379537321152922133249457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586358214101948088832971 2379537321152922133249457)
          ·
            refine ⟨1784652990864691599937093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2379537321152922133249457 1784652990864691599937093)
            ·
              refine ⟨334622435787129674988205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1784652990864691599937093 334622435787129674988205)
              ·
                refine ⟨125483413420173628120577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334622435787129674988205 125483413420173628120577)
                ·
                  refine ⟨94112560065130221090433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125483413420173628120577 94112560065130221090433)
                  ·
                    rfl

theorem cell20_206194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_206194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206194 prefixEnd_206194 := by exact prefixLift 206194
  have htrace : WordTrace (prefixWord ++ tailWord_206194) baseStart_206194 baseEnd_206194 := by
    simpa [prefixWord, tailWord_206194, baseEnd_206194] using wordTrace_append hprefix tailTrace_206194
  have hstable : (prefixWord ++ tailWord_206194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206194).length < 2 ^ (prefixWord ++ tailWord_206194).sum := by decide
  have hdescent : baseEnd_206194 < baseStart_206194 := by decide
  rcases family_descends (prefixWord ++ tailWord_206194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206205 : List Nat := [1, 4, 1, 1, 2, 2, 9]
def baseStart_206205 : Nat := 118140960795 + 206205 * 2 ^ 59
def prefixEnd_206205 : Nat := 4983230072969 + 3 ^ 40 * 206205 * 2
def baseEnd_206205 : Nat := 10457508973873674635969

theorem tailTrace_206205 : CollatzResearch.WordTrace tailWord_206205 prefixEnd_206205 10457508973873674635969 := by
  unfold tailWord_206205
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520914217961976855340069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5013942811974651236893379 7520914217961976855340069)
  ·
    refine ⟨1410171415867870660376263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7520914217961976855340069 1410171415867870660376263)
    ·
      refine ⟨2115257123801805990564395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410171415867870660376263 2115257123801805990564395)
      ·
        refine ⟨3172885685702708985846593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115257123801805990564395 3172885685702708985846593)
        ·
          refine ⟨2379664264277031739384945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3172885685702708985846593 2379664264277031739384945)
          ·
            refine ⟨1784748198207773804538709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2379664264277031739384945 1784748198207773804538709)
            ·
              refine ⟨10457508973873674635969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1784748198207773804538709 10457508973873674635969)
              ·
                rfl

theorem cell20_206205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 9].length) (baseStart_206205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206205 prefixEnd_206205 := by exact prefixLift 206205
  have htrace : WordTrace (prefixWord ++ tailWord_206205) baseStart_206205 baseEnd_206205 := by
    simpa [prefixWord, tailWord_206205, baseEnd_206205] using wordTrace_append hprefix tailTrace_206205
  have hstable : (prefixWord ++ tailWord_206205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206205).length < 2 ^ (prefixWord ++ tailWord_206205).sum := by decide
  have hdescent : baseEnd_206205 < baseStart_206205 := by decide
  rcases family_descends (prefixWord ++ tailWord_206205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206215 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 4]
def baseStart_206215 : Nat := 118140960795 + 206215 * 2 ^ 59
def prefixEnd_206215 : Nat := 4983230072969 + 3 ^ 40 * 206215 * 2
def baseEnd_206215 : Nat := 94122145037347481390347

theorem tailTrace_206215 : CollatzResearch.WordTrace tailWord_206215 prefixEnd_206215 94122145037347481390347 := by
  unfold tailWord_206215
  simp only [CollatzResearch.WordTrace]
  refine ⟨7521278947925748563204099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5014185965283832375469399 7521278947925748563204099)
  ·
    refine ⟨11281918421888622844806149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7521278947925748563204099 11281918421888622844806149)
    ·
      refine ⟨2115359704104116783401153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11281918421888622844806149 2115359704104116783401153)
      ·
        refine ⟨1586519778078087587550865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2115359704104116783401153 1586519778078087587550865)
        ·
          refine ⟨1189889833558565690663149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586519778078087587550865 1189889833558565690663149)
          ·
            refine ⟨446208687584462133998681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1189889833558565690663149 446208687584462133998681)
            ·
              refine ⟨334656515688346600499011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446208687584462133998681 334656515688346600499011)
              ·
                refine ⟨501984773532519900748517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334656515688346600499011 501984773532519900748517)
                ·
                  refine ⟨94122145037347481390347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 501984773532519900748517 94122145037347481390347)
                  ·
                    rfl

theorem cell20_206215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_206215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206215 prefixEnd_206215 := by exact prefixLift 206215
  have htrace : WordTrace (prefixWord ++ tailWord_206215) baseStart_206215 baseEnd_206215 := by
    simpa [prefixWord, tailWord_206215, baseEnd_206215] using wordTrace_append hprefix tailTrace_206215
  have hstable : (prefixWord ++ tailWord_206215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206215).length < 2 ^ (prefixWord ++ tailWord_206215).sum := by decide
  have hdescent : baseEnd_206215 < baseStart_206215 := by decide
  rcases family_descends (prefixWord ++ tailWord_206215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206229 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 3]
def baseStart_206229 : Nat := 118140960795 + 206229 * 2 ^ 59
def prefixEnd_206229 : Nat := 4983230072969 + 3 ^ 40 * 206229 * 2
def baseEnd_206229 : Nat := 94128535018825654923623

theorem tailTrace_206229 : CollatzResearch.WordTrace tailWord_206229 prefixEnd_206229 94128535018825654923623 := by
  unfold tailWord_206229
  simp only [CollatzResearch.WordTrace]
  refine ⟨7521789569875028954213741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5014526379916685969475827 7521789569875028954213741)
  ·
    refine ⟨2820671088703135857830153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7521789569875028954213741 2820671088703135857830153)
    ·
      refine ⟨2115503316527351893372615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2820671088703135857830153 2115503316527351893372615)
      ·
        refine ⟨3173254974791027840058923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115503316527351893372615 3173254974791027840058923)
        ·
          refine ⟨4759882462186541760088385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173254974791027840058923 4759882462186541760088385)
          ·
            refine ⟨3569911846639906320066289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4759882462186541760088385 3569911846639906320066289)
            ·
              refine ⟨2677433884979929740049717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569911846639906320066289 2677433884979929740049717)
              ·
                refine ⟨251009426716868413129661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2677433884979929740049717 251009426716868413129661)
                ·
                  refine ⟨94128535018825654923623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251009426716868413129661 94128535018825654923623)
                  ·
                    rfl

theorem cell20_206229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_206229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206229 prefixEnd_206229 := by exact prefixLift 206229
  have htrace : WordTrace (prefixWord ++ tailWord_206229) baseStart_206229 baseEnd_206229 := by
    simpa [prefixWord, tailWord_206229, baseEnd_206229] using wordTrace_append hprefix tailTrace_206229
  have hstable : (prefixWord ++ tailWord_206229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206229).length < 2 ^ (prefixWord ++ tailWord_206229).sum := by decide
  have hdescent : baseEnd_206229 < baseStart_206229 := by decide
  rcases family_descends (prefixWord ++ tailWord_206229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206239 : List Nat := [1, 1, 2, 5, 1, 4, 2, 4]
def baseStart_206239 : Nat := 118140960795 + 206239 * 2 ^ 59
def prefixEnd_206239 : Nat := 4983230072969 + 3 ^ 40 * 206239 * 2
def baseEnd_206239 : Nat := 31377699763770021530083

theorem tailTrace_206239 : CollatzResearch.WordTrace tailWord_206239 prefixEnd_206239 31377699763770021530083 := by
  unfold tailWord_206239
  simp only [CollatzResearch.WordTrace]
  refine ⟨7522154299838800662077771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5014769533225867108051847 7522154299838800662077771)
  ·
    refine ⟨11283231449758200993116657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7522154299838800662077771 11283231449758200993116657)
    ·
      refine ⟨8462423587318650744837493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11283231449758200993116657 8462423587318650744837493)
      ·
        refine ⟨793352211311123507328515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8462423587318650744837493 793352211311123507328515)
        ·
          refine ⟨1190028316966685260992773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793352211311123507328515 1190028316966685260992773)
          ·
            refine ⟨223130309431253486436145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1190028316966685260992773 223130309431253486436145)
            ·
              refine ⟨167347732073440114827109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223130309431253486436145 167347732073440114827109)
              ·
                refine ⟨31377699763770021530083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167347732073440114827109 31377699763770021530083)
                ·
                  rfl

theorem cell20_206239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 4].length) (baseStart_206239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206239 prefixEnd_206239 := by exact prefixLift 206239
  have htrace : WordTrace (prefixWord ++ tailWord_206239) baseStart_206239 baseEnd_206239 := by
    simpa [prefixWord, tailWord_206239, baseEnd_206239] using wordTrace_append hprefix tailTrace_206239
  have hstable : (prefixWord ++ tailWord_206239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206239).length < 2 ^ (prefixWord ++ tailWord_206239).sum := by decide
  have hdescent : baseEnd_206239 < baseStart_206239 := by decide
  rcases family_descends (prefixWord ++ tailWord_206239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206243 : List Nat := [1, 1, 1, 4, 1, 3, 3, 6]
def baseStart_206243 : Nat := 118140960795 + 206243 * 2 ^ 59
def prefixEnd_206243 : Nat := 4983230072969 + 3 ^ 40 * 206243 * 2
def baseEnd_206243 : Nat := 31378308333434609485633

theorem tailTrace_206243 : CollatzResearch.WordTrace tailWord_206243 prefixEnd_206243 31378308333434609485633 := by
  unfold tailWord_206243
  simp only [CollatzResearch.WordTrace]
  refine ⟨7522300191824309345223383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5014866794549539563482255 7522300191824309345223383)
  ·
    refine ⟨11283450287736464017835075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7522300191824309345223383 11283450287736464017835075)
    ·
      refine ⟨16925175431604696026752613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11283450287736464017835075 16925175431604696026752613)
      ·
        refine ⟨3173470393425880505016115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16925175431604696026752613 3173470393425880505016115)
        ·
          refine ⟨4760205590138820757524173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173470393425880505016115 4760205590138820757524173)
          ·
            refine ⟨1785077096302057784071565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4760205590138820757524173 1785077096302057784071565)
            ·
              refine ⟨669403911113271669026837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1785077096302057784071565 669403911113271669026837)
              ·
                refine ⟨31378308333434609485633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 669403911113271669026837 31378308333434609485633)
                ·
                  rfl

theorem cell20_206243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_206243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206243 prefixEnd_206243 := by exact prefixLift 206243
  have htrace : WordTrace (prefixWord ++ tailWord_206243) baseStart_206243 baseEnd_206243 := by
    simpa [prefixWord, tailWord_206243, baseEnd_206243] using wordTrace_append hprefix tailTrace_206243
  have hstable : (prefixWord ++ tailWord_206243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206243).length < 2 ^ (prefixWord ++ tailWord_206243).sum := by decide
  have hdescent : baseEnd_206243 < baseStart_206243 := by decide
  rcases family_descends (prefixWord ++ tailWord_206243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206284 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 3]
def baseStart_206284 : Nat := 118140960795 + 206284 * 2 ^ 59
def prefixEnd_206284 : Nat := 4983230072969 + 3 ^ 40 * 206284 * 2
def baseEnd_206284 : Nat := 94153638517489908090065

theorem tailTrace_206284 : CollatzResearch.WordTrace tailWord_206284 prefixEnd_206284 94153638517489908090065 := by
  unfold tailWord_206284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3761897792337886673732953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5015863723117182231643937 3761897792337886673732953)
  ·
    refine ⟨2821423344253415005299715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3761897792337886673732953 2821423344253415005299715)
    ·
      refine ⟨4232135016380122507949573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2821423344253415005299715 4232135016380122507949573)
      ·
        refine ⟨793525315571272970240545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4232135016380122507949573 793525315571272970240545)
        ·
          refine ⟨595143986678454727680409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793525315571272970240545 595143986678454727680409)
          ·
            refine ⟨446357990008841045760307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595143986678454727680409 446357990008841045760307)
            ·
              refine ⟨669536985013261568640461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446357990008841045760307 669536985013261568640461)
              ·
                refine ⟨251076369379973088240173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669536985013261568640461 251076369379973088240173)
                ·
                  refine ⟨94153638517489908090065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251076369379973088240173 94153638517489908090065)
                  ·
                    rfl

theorem cell20_206284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_206284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206284 prefixEnd_206284 := by exact prefixLift 206284
  have htrace : WordTrace (prefixWord ++ tailWord_206284) baseStart_206284 baseEnd_206284 := by
    simpa [prefixWord, tailWord_206284, baseEnd_206284] using wordTrace_append hprefix tailTrace_206284
  have hstable : (prefixWord ++ tailWord_206284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206284).length < 2 ^ (prefixWord ++ tailWord_206284).sum := by decide
  have hdescent : baseEnd_206284 < baseStart_206284 := by decide
  rcases family_descends (prefixWord ++ tailWord_206284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206322 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_206322 : Nat := 118140960795 + 206322 * 2 ^ 59
def prefixEnd_206322 : Nat := 4983230072969 + 3 ^ 40 * 206322 * 2
def baseEnd_206322 : Nat := 94170982752930664823243

theorem tailTrace_206322 : CollatzResearch.WordTrace tailWord_206322 prefixEnd_206322 94170982752930664823243 := by
  unfold tailWord_206322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1881295389634526459337305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5016787705692070558232813 1881295389634526459337305)
  ·
    refine ⟨1410971542225894844502979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1881295389634526459337305 1410971542225894844502979)
    ·
      refine ⟨2116457313338842266754469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410971542225894844502979 2116457313338842266754469)
      ·
        refine ⟨396835746251032925016463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2116457313338842266754469 396835746251032925016463)
        ·
          refine ⟨595253619376549387524695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396835746251032925016463 595253619376549387524695)
          ·
            refine ⟨892880429064824081287043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595253619376549387524695 892880429064824081287043)
            ·
              refine ⟨1339320643597236121930565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892880429064824081287043 1339320643597236121930565)
              ·
                refine ⟨251122620674481772861981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1339320643597236121930565 251122620674481772861981)
                ·
                  refine ⟨94170982752930664823243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251122620674481772861981 94170982752930664823243)
                  ·
                    rfl

theorem cell20_206322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_206322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206322 prefixEnd_206322 := by exact prefixLift 206322
  have htrace : WordTrace (prefixWord ++ tailWord_206322) baseStart_206322 baseEnd_206322 := by
    simpa [prefixWord, tailWord_206322, baseEnd_206322] using wordTrace_append hprefix tailTrace_206322
  have hstable : (prefixWord ++ tailWord_206322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206322).length < 2 ^ (prefixWord ++ tailWord_206322).sum := by decide
  have hdescent : baseEnd_206322 < baseStart_206322 := by decide
  rcases family_descends (prefixWord ++ tailWord_206322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206325 : List Nat := [1, 3, 5, 1, 1, 2, 1, 4, 2]
def baseStart_206325 : Nat := 118140960795 + 206325 * 2 ^ 59
def prefixEnd_206325 : Nat := 4983230072969 + 3 ^ 40 * 206325 * 2
def baseEnd_206325 : Nat := 94172352034675987723231

theorem tailTrace_206325 : CollatzResearch.WordTrace tailWord_206325 prefixEnd_206325 94172352034675987723231 := by
  unfold tailWord_206325
  simp only [CollatzResearch.WordTrace]
  refine ⟨7525290977527237349708429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5016860651684824899805619 7525290977527237349708429)
  ·
    refine ⟨2821984116572714006140661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7525290977527237349708429 2821984116572714006140661)
    ·
      refine ⟨264561010928691938075687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2821984116572714006140661 264561010928691938075687)
      ·
        refine ⟨396841516393037907113531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264561010928691938075687 396841516393037907113531)
        ·
          refine ⟨595262274589556860670297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396841516393037907113531 595262274589556860670297)
          ·
            refine ⟨446446705942167645502723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595262274589556860670297 446446705942167645502723)
            ·
              refine ⟨669670058913251468254085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446446705942167645502723 669670058913251468254085)
              ·
                refine ⟨125563136046234650297641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669670058913251468254085 125563136046234650297641)
                ·
                  refine ⟨94172352034675987723231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125563136046234650297641 94172352034675987723231)
                  ·
                    rfl

theorem cell20_206325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_206325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206325 prefixEnd_206325 := by exact prefixLift 206325
  have htrace : WordTrace (prefixWord ++ tailWord_206325) baseStart_206325 baseEnd_206325 := by
    simpa [prefixWord, tailWord_206325, baseEnd_206325] using wordTrace_append hprefix tailTrace_206325
  have hstable : (prefixWord ++ tailWord_206325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206325).length < 2 ^ (prefixWord ++ tailWord_206325).sum := by decide
  have hdescent : baseEnd_206325 < baseStart_206325 := by decide
  rcases family_descends (prefixWord ++ tailWord_206325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206342 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_206342 : Nat := 118140960795 + 206342 * 2 ^ 59
def prefixEnd_206342 : Nat := 4983230072969 + 3 ^ 40 * 206342 * 2
def baseEnd_206342 : Nat := 94180111297899484156495

theorem tailTrace_206342 : CollatzResearch.WordTrace tailWord_206342 prefixEnd_206342 94180111297899484156495 := by
  unfold tailWord_206342
  simp only [CollatzResearch.WordTrace]
  refine ⟨235184719327051539158665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5017274012310432835384853 235184719327051539158665)
  ·
    refine ⟨176388539495288654368999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235184719327051539158665 176388539495288654368999)
    ·
      refine ⟨264582809242932981553499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176388539495288654368999 264582809242932981553499)
      ·
        refine ⟨396874213864399472330249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264582809242932981553499 396874213864399472330249)
        ·
          refine ⟨297655660398299604247687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396874213864399472330249 297655660398299604247687)
          ·
            refine ⟨446483490597449406371531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297655660398299604247687 446483490597449406371531)
            ·
              refine ⟨669725235896174109557297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446483490597449406371531 669725235896174109557297)
              ·
                refine ⟨502293926922130582167973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669725235896174109557297 502293926922130582167973)
                ·
                  refine ⟨94180111297899484156495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502293926922130582167973 94180111297899484156495)
                  ·
                    rfl

theorem cell20_206342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_206342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206342 prefixEnd_206342 := by exact prefixLift 206342
  have htrace : WordTrace (prefixWord ++ tailWord_206342) baseStart_206342 baseEnd_206342 := by
    simpa [prefixWord, tailWord_206342, baseEnd_206342] using wordTrace_append hprefix tailTrace_206342
  have hstable : (prefixWord ++ tailWord_206342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206342).length < 2 ^ (prefixWord ++ tailWord_206342).sum := by decide
  have hdescent : baseEnd_206342 < baseStart_206342 := by decide
  rcases family_descends (prefixWord ++ tailWord_206342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206349 : List Nat := [1, 7, 1, 1, 2, 1, 3, 4]
def baseStart_206349 : Nat := 118140960795 + 206349 * 2 ^ 59
def prefixEnd_206349 : Nat := 4983230072969 + 3 ^ 40 * 206349 * 2
def baseEnd_206349 : Nat := 31394435429546190307711

theorem tailTrace_206349 : CollatzResearch.WordTrace tailWord_206349 prefixEnd_206349 31394435429546190307711 := by
  unfold tailWord_206349
  simp only [CollatzResearch.WordTrace]
  refine ⟨7526166329440289448582101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5017444219626859632388067 7526166329440289448582101)
  ·
    refine ⟨176394523346256783951143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7526166329440289448582101 176394523346256783951143)
    ·
      refine ⟨264591785019385175926715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176394523346256783951143 264591785019385175926715)
      ·
        refine ⟨396887677529077763890073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264591785019385175926715 396887677529077763890073)
        ·
          refine ⟨297665758146808322917555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396887677529077763890073 297665758146808322917555)
          ·
            refine ⟨446498637220212484376333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297665758146808322917555 446498637220212484376333)
            ·
              refine ⟨167436988957579681641125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446498637220212484376333 167436988957579681641125)
              ·
                refine ⟨31394435429546190307711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167436988957579681641125 31394435429546190307711)
                ·
                  rfl

theorem cell20_206349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 4].length) (baseStart_206349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206349 prefixEnd_206349 := by exact prefixLift 206349
  have htrace : WordTrace (prefixWord ++ tailWord_206349) baseStart_206349 baseEnd_206349 := by
    simpa [prefixWord, tailWord_206349, baseEnd_206349] using wordTrace_append hprefix tailTrace_206349
  have hstable : (prefixWord ++ tailWord_206349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206349).length < 2 ^ (prefixWord ++ tailWord_206349).sum := by decide
  have hdescent : baseEnd_206349 < baseStart_206349 := by decide
  rcases family_descends (prefixWord ++ tailWord_206349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206367 : List Nat := [1, 1, 2, 4, 1, 1, 3, 5, 2]
def baseStart_206367 : Nat := 118140960795 + 206367 * 2 ^ 59
def prefixEnd_206367 : Nat := 4983230072969 + 3 ^ 40 * 206367 * 2
def baseEnd_206367 : Nat := 94191521979110508323059

theorem tailTrace_206367 : CollatzResearch.WordTrace tailWord_206367 prefixEnd_206367 94191521979110508323059 := by
  unfold tailWord_206367
  simp only [CollatzResearch.WordTrace]
  refine ⟨7526822843375078522737355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5017881895583385681824903 7526822843375078522737355)
  ·
    refine ⟨11290234265062617784106033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7526822843375078522737355 11290234265062617784106033)
    ·
      refine ⟨8467675698796963338079525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11290234265062617784106033 8467675698796963338079525)
      ·
        refine ⟨1587689193524430625889911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8467675698796963338079525 1587689193524430625889911)
        ·
          refine ⟨2381533790286645938834867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587689193524430625889911 2381533790286645938834867)
          ·
            refine ⟨3572300685429968908252301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381533790286645938834867 3572300685429968908252301)
            ·
              refine ⟨1339612757036238340594613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3572300685429968908252301 1339612757036238340594613)
              ·
                refine ⟨125588695972147344430745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1339612757036238340594613 125588695972147344430745)
                ·
                  refine ⟨94191521979110508323059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125588695972147344430745 94191521979110508323059)
                  ·
                    rfl

theorem cell20_206367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 2].length) (baseStart_206367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206367 prefixEnd_206367 := by exact prefixLift 206367
  have htrace : WordTrace (prefixWord ++ tailWord_206367) baseStart_206367 baseEnd_206367 := by
    simpa [prefixWord, tailWord_206367, baseEnd_206367] using wordTrace_append hprefix tailTrace_206367
  have hstable : (prefixWord ++ tailWord_206367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206367).length < 2 ^ (prefixWord ++ tailWord_206367).sum := by decide
  have hdescent : baseEnd_206367 < baseStart_206367 := by decide
  rcases family_descends (prefixWord ++ tailWord_206367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206412 : List Nat := [2, 2, 1, 3, 1, 3, 4, 4]
def baseStart_206412 : Nat := 118140960795 + 206412 * 2 ^ 59
def prefixEnd_206412 : Nat := 4983230072969 + 3 ^ 40 * 206412 * 2
def baseEnd_206412 : Nat := 31404020401763450607625

theorem tailTrace_206412 : CollatzResearch.WordTrace tailWord_206412 prefixEnd_206412 31404020401763450607625 := by
  unfold tailWord_206412
  simp only [CollatzResearch.WordTrace]
  refine ⟨3764232064106025604062745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5018976085474700805416993 3764232064106025604062745)
  ·
    refine ⟨2823174048079519203047059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3764232064106025604062745 2823174048079519203047059)
    ·
      refine ⟨4234761072119278804570589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823174048079519203047059 4234761072119278804570589)
      ·
        refine ⟨1588035402044729551713971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4234761072119278804570589 1588035402044729551713971)
        ·
          refine ⟨2382053103067094327570957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588035402044729551713971 2382053103067094327570957)
          ·
            refine ⟨893269913650160372839109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2382053103067094327570957 893269913650160372839109)
            ·
              refine ⟨167488108809405069907333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 893269913650160372839109 167488108809405069907333)
              ·
                refine ⟨31404020401763450607625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167488108809405069907333 31404020401763450607625)
                ·
                  rfl

theorem cell20_206412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_206412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206412 prefixEnd_206412 := by exact prefixLift 206412
  have htrace : WordTrace (prefixWord ++ tailWord_206412) baseStart_206412 baseEnd_206412 := by
    simpa [prefixWord, tailWord_206412, baseEnd_206412] using wordTrace_append hprefix tailTrace_206412
  have hstable : (prefixWord ++ tailWord_206412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206412).length < 2 ^ (prefixWord ++ tailWord_206412).sum := by decide
  have hdescent : baseEnd_206412 < baseStart_206412 := by decide
  rcases family_descends (prefixWord ++ tailWord_206412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206450 : List Nat := [3, 2, 1, 2, 3, 2, 2, 5]
def baseStart_206450 : Nat := 118140960795 + 206450 * 2 ^ 59
def prefixEnd_206450 : Nat := 4983230072969 + 3 ^ 40 * 206450 * 2
def baseEnd_206450 : Nat := 31409801813577036185351

theorem tailTrace_206450 : CollatzResearch.WordTrace tailWord_206450 prefixEnd_206450 31409801813577036185351 := by
  unfold tailWord_206450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882462525518595924502201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5019900068049589132005869 1882462525518595924502201)
  ·
    refine ⟨1411846894138946943376651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1882462525518595924502201 1411846894138946943376651)
    ·
      refine ⟨2117770341208420415064977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1411846894138946943376651 2117770341208420415064977)
      ·
        refine ⟨1588327755906315311298733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2117770341208420415064977 1588327755906315311298733)
        ·
          refine ⟨595622908464868241737025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1588327755906315311298733 595622908464868241737025)
          ·
            refine ⟨446717181348651181302769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595622908464868241737025 446717181348651181302769)
            ·
              refine ⟨335037886011488385977077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446717181348651181302769 335037886011488385977077)
              ·
                refine ⟨31409801813577036185351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 335037886011488385977077 31409801813577036185351)
                ·
                  rfl

theorem cell20_206450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_206450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206450 prefixEnd_206450 := by exact prefixLift 206450
  have htrace : WordTrace (prefixWord ++ tailWord_206450) baseStart_206450 baseEnd_206450 := by
    simpa [prefixWord, tailWord_206450, baseEnd_206450] using wordTrace_append hprefix tailTrace_206450
  have hstable : (prefixWord ++ tailWord_206450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206450).length < 2 ^ (prefixWord ++ tailWord_206450).sum := by decide
  have hdescent : baseEnd_206450 < baseStart_206450 := by decide
  rcases family_descends (prefixWord ++ tailWord_206450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206453 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 3]
def baseStart_206453 : Nat := 118140960795 + 206453 * 2 ^ 59
def prefixEnd_206453 : Nat := 4983230072969 + 3 ^ 40 * 206453 * 2
def baseEnd_206453 : Nat := 94230774722476431456041

theorem tailTrace_206453 : CollatzResearch.WordTrace tailWord_206453 prefixEnd_206453 94230774722476431456041 := by
  unfold tailWord_206453
  simp only [CollatzResearch.WordTrace]
  refine ⟨7529959521063515210368013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5019973014042343473578675 7529959521063515210368013)
  ·
    refine ⟨2823734820398818203888005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7529959521063515210368013 2823734820398818203888005)
    ·
      refine ⟨529450278824778413229001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2823734820398818203888005 529450278824778413229001)
      ·
        refine ⟨397087709118583809921751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529450278824778413229001 397087709118583809921751)
        ·
          refine ⟨595631563677875714882627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397087709118583809921751 595631563677875714882627)
          ·
            refine ⟨893447345516813572323941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595631563677875714882627 893447345516813572323941)
            ·
              refine ⟨167521377284402544810739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 893447345516813572323941 167521377284402544810739)
              ·
                refine ⟨251282065926603817216109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167521377284402544810739 251282065926603817216109)
                ·
                  refine ⟨94230774722476431456041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251282065926603817216109 94230774722476431456041)
                  ·
                    rfl

theorem cell20_206453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_206453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206453 prefixEnd_206453 := by exact prefixLift 206453
  have htrace : WordTrace (prefixWord ++ tailWord_206453) baseStart_206453 baseEnd_206453 := by
    simpa [prefixWord, tailWord_206453, baseEnd_206453] using wordTrace_append hprefix tailTrace_206453
  have hstable : (prefixWord ++ tailWord_206453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206453).length < 2 ^ (prefixWord ++ tailWord_206453).sum := by decide
  have hdescent : baseEnd_206453 < baseStart_206453 := by decide
  rcases family_descends (prefixWord ++ tailWord_206453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206457 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 3]
def baseStart_206457 : Nat := 118140960795 + 206457 * 2 ^ 59
def prefixEnd_206457 : Nat := 4983230072969 + 3 ^ 40 * 206457 * 2
def baseEnd_206457 : Nat := 94232600431470195322691

theorem tailTrace_206457 : CollatzResearch.WordTrace tailWord_206457 prefixEnd_206457 94232600431470195322691 := by
  unfold tailWord_206457
  simp only [CollatzResearch.WordTrace]
  refine ⟨7530105413049023893513625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5020070275366015929009083 7530105413049023893513625)
  ·
    refine ⟨5647579059786767920135219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7530105413049023893513625 5647579059786767920135219)
    ·
      refine ⟨8471368589680151880202829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5647579059786767920135219 8471368589680151880202829)
      ·
        refine ⟨3176763221130056955076061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8471368589680151880202829 3176763221130056955076061)
        ·
          refine ⟨1191286207923771358153523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3176763221130056955076061 1191286207923771358153523)
          ·
            refine ⟨1786929311885657037230285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191286207923771358153523 1786929311885657037230285)
            ·
              refine ⟨670098491957121388961357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1786929311885657037230285 670098491957121388961357)
              ·
                refine ⟨251286934483920520860509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 670098491957121388961357 251286934483920520860509)
                ·
                  refine ⟨94232600431470195322691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251286934483920520860509 94232600431470195322691)
                  ·
                    rfl

theorem cell20_206457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_206457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206457 prefixEnd_206457 := by exact prefixLift 206457
  have htrace : WordTrace (prefixWord ++ tailWord_206457) baseStart_206457 baseEnd_206457 := by
    simpa [prefixWord, tailWord_206457, baseEnd_206457] using wordTrace_append hprefix tailTrace_206457
  have hstable : (prefixWord ++ tailWord_206457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206457).length < 2 ^ (prefixWord ++ tailWord_206457).sum := by decide
  have hdescent : baseEnd_206457 < baseStart_206457 := by decide
  rcases family_descends (prefixWord ++ tailWord_206457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206471 : List Nat := [1, 1, 4, 2, 1, 3, 2, 6]
def baseStart_206471 : Nat := 118140960795 + 206471 * 2 ^ 59
def prefixEnd_206471 : Nat := 4983230072969 + 3 ^ 40 * 206471 * 2
def baseEnd_206471 : Nat := 31412996804316122951989

theorem tailTrace_206471 : CollatzResearch.WordTrace tailWord_206471 prefixEnd_206471 31412996804316122951989 := by
  unfold tailWord_206471
  simp only [CollatzResearch.WordTrace]
  refine ⟨7530616034998304284523267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5020410689998869523015511 7530616034998304284523267)
  ·
    refine ⟨11295924052497456426784901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7530616034998304284523267 11295924052497456426784901)
    ·
      refine ⟨2117985759843273080022169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11295924052497456426784901 2117985759843273080022169)
      ·
        refine ⟨1588489319882454810016627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2117985759843273080022169 1588489319882454810016627)
        ·
          refine ⟨2382733979823682215024941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588489319882454810016627 2382733979823682215024941)
          ·
            refine ⟨893525242433880830634353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2382733979823682215024941 893525242433880830634353)
            ·
              refine ⟨670143931825410622975765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893525242433880830634353 670143931825410622975765)
              ·
                refine ⟨31412996804316122951989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 670143931825410622975765 31412996804316122951989)
                ·
                  rfl

theorem cell20_206471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_206471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206471 prefixEnd_206471 := by exact prefixLift 206471
  have htrace : WordTrace (prefixWord ++ tailWord_206471) baseStart_206471 baseEnd_206471 := by
    simpa [prefixWord, tailWord_206471, baseEnd_206471] using wordTrace_append hprefix tailTrace_206471
  have hstable : (prefixWord ++ tailWord_206471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206471).length < 2 ^ (prefixWord ++ tailWord_206471).sum := by decide
  have hdescent : baseEnd_206471 < baseStart_206471 := by decide
  rcases family_descends (prefixWord ++ tailWord_206471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206494 : List Nat := [4, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_206494 : Nat := 118140960795 + 206494 * 2 ^ 59
def prefixEnd_206494 : Nat := 4983230072969 + 3 ^ 40 * 206494 * 2
def baseEnd_206494 : Nat := 94249488239662511089207

theorem tailTrace_206494 : CollatzResearch.WordTrace tailWord_206494 prefixEnd_206494 94249488239662511089207 := by
  unfold tailWord_206494
  simp only [CollatzResearch.WordTrace]
  refine ⟨941431864239372401576317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5020969942609986141740357 941431864239372401576317)
  ·
    refine ⟨353036949089764650591119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 941431864239372401576317 353036949089764650591119)
    ·
      refine ⟨529555423634646975886679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353036949089764650591119 529555423634646975886679)
      ·
        refine ⟨794333135451970463830019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529555423634646975886679 794333135451970463830019)
        ·
          refine ⟨1191499703177955695745029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794333135451970463830019 1191499703177955695745029)
          ·
            refine ⟨223406194345866692952193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1191499703177955695745029 223406194345866692952193)
            ·
              refine ⟨167554645759400019714145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223406194345866692952193 167554645759400019714145)
              ·
                refine ⟨125665984319550014785609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167554645759400019714145 125665984319550014785609)
                ·
                  refine ⟨94249488239662511089207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125665984319550014785609 94249488239662511089207)
                  ·
                    rfl

theorem cell20_206494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_206494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206494 prefixEnd_206494 := by exact prefixLift 206494
  have htrace : WordTrace (prefixWord ++ tailWord_206494) baseStart_206494 baseEnd_206494 := by
    simpa [prefixWord, tailWord_206494, baseEnd_206494] using wordTrace_append hprefix tailTrace_206494
  have hstable : (prefixWord ++ tailWord_206494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206494).length < 2 ^ (prefixWord ++ tailWord_206494).sum := by decide
  have hdescent : baseEnd_206494 < baseStart_206494 := by decide
  rcases family_descends (prefixWord ++ tailWord_206494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206578 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_206578 : Nat := 118140960795 + 206578 * 2 ^ 59
def prefixEnd_206578 : Nat := 4983230072969 + 3 ^ 40 * 206578 * 2
def baseEnd_206578 : Nat := 94287828128531552288863

theorem tailTrace_206578 : CollatzResearch.WordTrace tailWord_206578 prefixEnd_206578 94287828128531552288863 := by
  unfold tailWord_206578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883629661402665389667097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5023012430407107705778925 1883629661402665389667097)
  ·
    refine ⟨1412722246051999042250323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1883629661402665389667097 1412722246051999042250323)
    ·
      refine ⟨2119083369077998563375485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1412722246051999042250323 2119083369077998563375485)
      ·
        refine ⟨794656263404249461265807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2119083369077998563375485 794656263404249461265807)
        ·
          refine ⟨1191984395106374191898711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794656263404249461265807 1191984395106374191898711)
          ·
            refine ⟨1787976592659561287848067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191984395106374191898711 1787976592659561287848067)
            ·
              refine ⟨2681964888989341931772101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787976592659561287848067 2681964888989341931772101)
              ·
                refine ⟨502868416685501612207269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2681964888989341931772101 502868416685501612207269)
                ·
                  refine ⟨94287828128531552288863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502868416685501612207269 94287828128531552288863)
                  ·
                    rfl

theorem cell20_206578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_206578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206578 prefixEnd_206578 := by exact prefixLift 206578
  have htrace : WordTrace (prefixWord ++ tailWord_206578) baseStart_206578 baseEnd_206578 := by
    simpa [prefixWord, tailWord_206578, baseEnd_206578] using wordTrace_append hprefix tailTrace_206578
  have hstable : (prefixWord ++ tailWord_206578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206578).length < 2 ^ (prefixWord ++ tailWord_206578).sum := by decide
  have hdescent : baseEnd_206578 < baseStart_206578 := by decide
  rcases family_descends (prefixWord ++ tailWord_206578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206595 : List Nat := [1, 1, 1, 3, 2, 2, 5, 3, 2]
def baseStart_206595 : Nat := 118140960795 + 206595 * 2 ^ 59
def prefixEnd_206595 : Nat := 4983230072969 + 3 ^ 40 * 206595 * 2
def baseEnd_206595 : Nat := 94295587391755048722127

theorem tailTrace_206595 : CollatzResearch.WordTrace tailWord_206595 prefixEnd_206595 94295587391755048722127 := by
  unfold tailWord_206595
  simp only [CollatzResearch.WordTrace]
  refine ⟨7535138686549073462037239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5023425791032715641358159 7535138686549073462037239)
  ·
    refine ⟨11302708029823610193055859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7535138686549073462037239 11302708029823610193055859)
    ·
      refine ⟨16954062044735415289583789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11302708029823610193055859 16954062044735415289583789)
      ·
        refine ⟨6357773266775780733593921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16954062044735415289583789 6357773266775780733593921)
        ·
          refine ⟨4768329950081835550195441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6357773266775780733593921 4768329950081835550195441)
          ·
            refine ⟨3576247462561376662646581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4768329950081835550195441 3576247462561376662646581)
            ·
              refine ⟨335273199615129062123117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3576247462561376662646581 335273199615129062123117)
              ·
                refine ⟨125727449855673398296169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335273199615129062123117 125727449855673398296169)
                ·
                  refine ⟨94295587391755048722127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125727449855673398296169 94295587391755048722127)
                  ·
                    rfl

theorem cell20_206595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 2].length) (baseStart_206595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206595 prefixEnd_206595 := by exact prefixLift 206595
  have htrace : WordTrace (prefixWord ++ tailWord_206595) baseStart_206595 baseEnd_206595 := by
    simpa [prefixWord, tailWord_206595, baseEnd_206595] using wordTrace_append hprefix tailTrace_206595
  have hstable : (prefixWord ++ tailWord_206595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206595).length < 2 ^ (prefixWord ++ tailWord_206595).sum := by decide
  have hdescent : baseEnd_206595 < baseStart_206595 := by decide
  rcases family_descends (prefixWord ++ tailWord_206595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206616 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_206616 : Nat := 118140960795 + 206616 * 2 ^ 59
def prefixEnd_206616 : Nat := 4983230072969 + 3 ^ 40 * 206616 * 2
def baseEnd_206616 : Nat := 94305172363972309022041

theorem tailTrace_206616 : CollatzResearch.WordTrace tailWord_206616 prefixEnd_206616 94305172363972309022041 := by
  unfold tailWord_206616
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767952309736497024275851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5023936412981996032367801 3767952309736497024275851)
  ·
    refine ⟨5651928464604745536413777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3767952309736497024275851 5651928464604745536413777)
    ·
      refine ⟨4238946348453559152310333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5651928464604745536413777 4238946348453559152310333)
      ·
        refine ⟨1589604880670084682116375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4238946348453559152310333 1589604880670084682116375)
        ·
          refine ⟨2384407321005127023174563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589604880670084682116375 2384407321005127023174563)
          ·
            refine ⟨3576610981507690534761845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384407321005127023174563 3576610981507690534761845)
            ·
              refine ⟨335307279516345987633923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3576610981507690534761845 335307279516345987633923)
              ·
                refine ⟨502960919274518981450885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335307279516345987633923 502960919274518981450885)
                ·
                  refine ⟨94305172363972309022041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502960919274518981450885 94305172363972309022041)
                  ·
                    rfl

theorem cell20_206616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_206616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206616 prefixEnd_206616 := by exact prefixLift 206616
  have htrace : WordTrace (prefixWord ++ tailWord_206616) baseStart_206616 baseEnd_206616 := by
    simpa [prefixWord, tailWord_206616, baseEnd_206616] using wordTrace_append hprefix tailTrace_206616
  have hstable : (prefixWord ++ tailWord_206616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206616).length < 2 ^ (prefixWord ++ tailWord_206616).sum := by decide
  have hdescent : baseEnd_206616 < baseStart_206616 := by decide
  rcases family_descends (prefixWord ++ tailWord_206616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206622 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_206622 : Nat := 118140960795 + 206622 * 2 ^ 59
def prefixEnd_206622 : Nat := 4983230072969 + 3 ^ 40 * 206622 * 2
def baseEnd_206622 : Nat := 94307910927462954822017

theorem tailTrace_206622 : CollatzResearch.WordTrace tailWord_206622 prefixEnd_206622 94307910927462954822017 := by
  unfold tailWord_206622
  simp only [CollatzResearch.WordTrace]
  refine ⟨942015432181407134158765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5024082304967504715513413 942015432181407134158765)
  ·
    refine ⟨353255787068027675309537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 942015432181407134158765 353255787068027675309537)
    ·
      refine ⟨264941840301020756482153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353255787068027675309537 264941840301020756482153)
      ·
        refine ⟨198706380225765567361615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264941840301020756482153 198706380225765567361615)
        ·
          refine ⟨298059570338648351042423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198706380225765567361615 298059570338648351042423)
          ·
            refine ⟨447089355507972526563635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298059570338648351042423 447089355507972526563635)
            ·
              refine ⟨670634033261958789845453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447089355507972526563635 670634033261958789845453)
              ·
                refine ⟨251487762473234546192045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 670634033261958789845453 251487762473234546192045)
                ·
                  refine ⟨94307910927462954822017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251487762473234546192045 94307910927462954822017)
                  ·
                    rfl

theorem cell20_206622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_206622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206622 prefixEnd_206622 := by exact prefixLift 206622
  have htrace : WordTrace (prefixWord ++ tailWord_206622) baseStart_206622 baseEnd_206622 := by
    simpa [prefixWord, tailWord_206622, baseEnd_206622] using wordTrace_append hprefix tailTrace_206622
  have hstable : (prefixWord ++ tailWord_206622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206622).length < 2 ^ (prefixWord ++ tailWord_206622).sum := by decide
  have hdescent : baseEnd_206622 < baseStart_206622 := by decide
  rcases family_descends (prefixWord ++ tailWord_206622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206623 : List Nat := [1, 1, 2, 4, 2, 1, 4, 5]
def baseStart_206623 : Nat := 118140960795 + 206623 * 2 ^ 59
def prefixEnd_206623 : Nat := 4983230072969 + 3 ^ 40 * 206623 * 2
def baseEnd_206623 : Nat := 31436122451570465262893

theorem tailTrace_206623 : CollatzResearch.WordTrace tailWord_206623 prefixEnd_206623 31436122451570465262893 := by
  unfold tailWord_206623
  simp only [CollatzResearch.WordTrace]
  refine ⟨7536159930447634244056523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5024106620298422829371015 7536159930447634244056523)
  ·
    refine ⟨11304239895671451366084785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7536159930447634244056523 11304239895671451366084785)
    ·
      refine ⟨8478179921753588524563589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11304239895671451366084785 8478179921753588524563589)
      ·
        refine ⟨1589658735328797848355673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8478179921753588524563589 1589658735328797848355673)
        ·
          refine ⟨1192244051496598386266755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589658735328797848355673 1192244051496598386266755)
          ·
            refine ⟨1788366077244897579400133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192244051496598386266755 1788366077244897579400133)
            ·
              refine ⟨335318639483418296137525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1788366077244897579400133 335318639483418296137525)
              ·
                refine ⟨31436122451570465262893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 335318639483418296137525 31436122451570465262893)
                ·
                  rfl

theorem cell20_206623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_206623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206623 prefixEnd_206623 := by exact prefixLift 206623
  have htrace : WordTrace (prefixWord ++ tailWord_206623) baseStart_206623 baseEnd_206623 := by
    simpa [prefixWord, tailWord_206623, baseEnd_206623] using wordTrace_append hprefix tailTrace_206623
  have hstable : (prefixWord ++ tailWord_206623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206623).length < 2 ^ (prefixWord ++ tailWord_206623).sum := by decide
  have hdescent : baseEnd_206623 < baseStart_206623 := by decide
  rcases family_descends (prefixWord ++ tailWord_206623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206706 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_206706 : Nat := 118140960795 + 206706 * 2 ^ 59
def prefixEnd_206706 : Nat := 4983230072969 + 3 ^ 40 * 206706 * 2
def baseEnd_206706 : Nat := 94346250816331996021673

theorem tailTrace_206706 : CollatzResearch.WordTrace tailWord_206706 prefixEnd_206706 94346250816331996021673 := by
  unfold tailWord_206706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1884796797286734854831993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5026124792764626279551981 1884796797286734854831993)
  ·
    refine ⟨1413597597965051141123995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1884796797286734854831993 1413597597965051141123995)
    ·
      refine ⟨2120396396947576711685993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1413597597965051141123995 2120396396947576711685993)
      ·
        refine ⟨1590297297710682533764495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2120396396947576711685993 1590297297710682533764495)
        ·
          refine ⟨2385445946566023800646743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590297297710682533764495 2385445946566023800646743)
          ·
            refine ⟨3578168919849035700970115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385445946566023800646743 3578168919849035700970115)
            ·
              refine ⟨5367253379773553551455173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578168919849035700970115 5367253379773553551455173)
              ·
                refine ⟨1006360008707541290897845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5367253379773553551455173 1006360008707541290897845)
                ·
                  refine ⟨94346250816331996021673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1006360008707541290897845 94346250816331996021673)
                  ·
                    rfl

theorem cell20_206706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_206706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206706 prefixEnd_206706 := by exact prefixLift 206706
  have htrace : WordTrace (prefixWord ++ tailWord_206706) baseStart_206706 baseEnd_206706 := by
    simpa [prefixWord, tailWord_206706, baseEnd_206706] using wordTrace_append hprefix tailTrace_206706
  have hstable : (prefixWord ++ tailWord_206706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206706).length < 2 ^ (prefixWord ++ tailWord_206706).sum := by decide
  have hdescent : baseEnd_206706 < baseStart_206706 := by decide
  rcases family_descends (prefixWord ++ tailWord_206706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206713 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_206713 : Nat := 118140960795 + 206713 * 2 ^ 59
def prefixEnd_206713 : Nat := 4983230072969 + 3 ^ 40 * 206713 * 2
def baseEnd_206713 : Nat := 94349445807071082788311

theorem tailTrace_206713 : CollatzResearch.WordTrace tailWord_206713 prefixEnd_206713 94349445807071082788311 := by
  unfold tailWord_206713
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539442500121579614832793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5026295000081053076555195 7539442500121579614832793)
  ·
    refine ⟨5654581875091184711124595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7539442500121579614832793 5654581875091184711124595)
    ·
      refine ⟨8481872812636777066686893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5654581875091184711124595 8481872812636777066686893)
      ·
        refine ⟨3180702304738791400007585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8481872812636777066686893 3180702304738791400007585)
        ·
          refine ⟨2385526728554093550005689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3180702304738791400007585 2385526728554093550005689)
          ·
            refine ⟨1789145046415570162504267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385526728554093550005689 1789145046415570162504267)
            ·
              refine ⟨2683717569623355243756401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789145046415570162504267 2683717569623355243756401)
              ·
                refine ⟨2012788177217516432817301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2683717569623355243756401 2012788177217516432817301)
                ·
                  refine ⟨94349445807071082788311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2012788177217516432817301 94349445807071082788311)
                  ·
                    rfl

theorem cell20_206713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_206713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206713 prefixEnd_206713 := by exact prefixLift 206713
  have htrace : WordTrace (prefixWord ++ tailWord_206713) baseStart_206713 baseEnd_206713 := by
    simpa [prefixWord, tailWord_206713, baseEnd_206713] using wordTrace_append hprefix tailTrace_206713
  have hstable : (prefixWord ++ tailWord_206713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206713).length < 2 ^ (prefixWord ++ tailWord_206713).sum := by decide
  have hdescent : baseEnd_206713 < baseStart_206713 := by decide
  rcases family_descends (prefixWord ++ tailWord_206713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206720 : List Nat := [2, 1, 1, 2, 1, 2, 11]
def baseStart_206720 : Nat := 118140960795 + 206720 * 2 ^ 59
def prefixEnd_206720 : Nat := 4983230072969 + 3 ^ 40 * 206720 * 2
def baseEnd_206720 : Nat := 10483626755312241061661

theorem tailTrace_206720 : CollatzResearch.WordTrace tailWord_206720 prefixEnd_206720 10483626755312241061661 := by
  unfold tailWord_206720
  simp only [CollatzResearch.WordTrace]
  refine ⟨3769848905548109905168807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5026465207397479873558409 3769848905548109905168807)
  ·
    refine ⟨5654773358322164857753211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3769848905548109905168807 5654773358322164857753211)
    ·
      refine ⟨8482160037483247286629817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5654773358322164857753211 8482160037483247286629817)
      ·
        refine ⟨6361620028112435464972363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8482160037483247286629817 6361620028112435464972363)
        ·
          refine ⟨9542430042168653197458545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361620028112435464972363 9542430042168653197458545)
          ·
            refine ⟨7156822531626489898093909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9542430042168653197458545 7156822531626489898093909)
            ·
              refine ⟨10483626755312241061661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7156822531626489898093909 10483626755312241061661)
              ·
                rfl

theorem cell20_206720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 11].length) (baseStart_206720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206720 prefixEnd_206720 := by exact prefixLift 206720
  have htrace : WordTrace (prefixWord ++ tailWord_206720) baseStart_206720 baseEnd_206720 := by
    simpa [prefixWord, tailWord_206720, baseEnd_206720] using wordTrace_append hprefix tailTrace_206720
  have hstable : (prefixWord ++ tailWord_206720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206720).length < 2 ^ (prefixWord ++ tailWord_206720).sum := by decide
  have hdescent : baseEnd_206720 < baseStart_206720 := by decide
  rcases family_descends (prefixWord ++ tailWord_206720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206723 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 3]
def baseStart_206723 : Nat := 118140960795 + 206723 * 2 ^ 59
def prefixEnd_206723 : Nat := 4983230072969 + 3 ^ 40 * 206723 * 2
def baseEnd_206723 : Nat := 94354010079555492454937

theorem tailTrace_206723 : CollatzResearch.WordTrace tailWord_206723 prefixEnd_206723 94354010079555492454937 := by
  unfold tailWord_206723
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539807230085351322696823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5026538153390234215131215 7539807230085351322696823)
  ·
    refine ⟨11309710845128026984045235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7539807230085351322696823 11309710845128026984045235)
    ·
      refine ⟨16964566267692040476067853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11309710845128026984045235 16964566267692040476067853)
      ·
        refine ⟨6361712350384515178525445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16964566267692040476067853 6361712350384515178525445)
        ·
          refine ⟨1192821065697096595973521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6361712350384515178525445 1192821065697096595973521)
          ·
            refine ⟨894615799272822446980141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192821065697096595973521 894615799272822446980141)
            ·
              refine ⟨335480924727308417617553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 894615799272822446980141 335480924727308417617553)
              ·
                refine ⟨251610693545481313213165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335480924727308417617553 251610693545481313213165)
                ·
                  refine ⟨94354010079555492454937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251610693545481313213165 94354010079555492454937)
                  ·
                    rfl

theorem cell20_206723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 3].length) (baseStart_206723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206723 prefixEnd_206723 := by exact prefixLift 206723
  have htrace : WordTrace (prefixWord ++ tailWord_206723) baseStart_206723 baseEnd_206723 := by
    simpa [prefixWord, tailWord_206723, baseEnd_206723] using wordTrace_append hprefix tailTrace_206723
  have hstable : (prefixWord ++ tailWord_206723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206723).length < 2 ^ (prefixWord ++ tailWord_206723).sum := by decide
  have hdescent : baseEnd_206723 < baseStart_206723 := by decide
  rcases family_descends (prefixWord ++ tailWord_206723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206754 : List Nat := [3, 3, 1, 2, 3, 1, 1, 6]
def baseStart_206754 : Nat := 118140960795 + 206754 * 2 ^ 59
def prefixEnd_206754 : Nat := 4983230072969 + 3 ^ 40 * 206754 * 2
def baseEnd_206754 : Nat := 31456053108085720807159

theorem tailTrace_206754 : CollatzResearch.WordTrace tailWord_206754 prefixEnd_206754 31456053108085720807159 := by
  unfold tailWord_206754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885234473243260904268829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5027291928648695744716877 1885234473243260904268829)
  ·
    refine ⟨706962927466222839100811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1885234473243260904268829 706962927466222839100811)
    ·
      refine ⟨1060444391199334258651217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706962927466222839100811 1060444391199334258651217)
      ·
        refine ⟨795333293399500693988413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1060444391199334258651217 795333293399500693988413)
        ·
          refine ⟨298249985024812760245655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795333293399500693988413 298249985024812760245655)
          ·
            refine ⟨447374977537219140368483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298249985024812760245655 447374977537219140368483)
            ·
              refine ⟨671062466305828710552725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447374977537219140368483 671062466305828710552725)
              ·
                refine ⟨31456053108085720807159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 671062466305828710552725 31456053108085720807159)
                ·
                  rfl

theorem cell20_206754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_206754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206754 prefixEnd_206754 := by exact prefixLift 206754
  have htrace : WordTrace (prefixWord ++ tailWord_206754) baseStart_206754 baseEnd_206754 := by
    simpa [prefixWord, tailWord_206754, baseEnd_206754] using wordTrace_append hprefix tailTrace_206754
  have hstable : (prefixWord ++ tailWord_206754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206754).length < 2 ^ (prefixWord ++ tailWord_206754).sum := by decide
  have hdescent : baseEnd_206754 < baseStart_206754 := by decide
  rcases family_descends (prefixWord ++ tailWord_206754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206760 : List Nat := [2, 1, 6, 2, 1, 2, 1, 3, 2]
def baseStart_206760 : Nat := 118140960795 + 206760 * 2 ^ 59
def prefixEnd_206760 : Nat := 4983230072969 + 3 ^ 40 * 206760 * 2
def baseEnd_206760 : Nat := 94370897887747808221453

theorem tailTrace_206760 : CollatzResearch.WordTrace tailWord_206760 prefixEnd_206760 94370897887747808221453 := by
  unfold tailWord_206760
  simp only [CollatzResearch.WordTrace]
  refine ⟨3770578365475653320896867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5027437820634204427862489 3770578365475653320896867)
  ·
    refine ⟨5655867548213479981345301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3770578365475653320896867 5655867548213479981345301)
    ·
      refine ⟨265118791322506874125561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5655867548213479981345301 265118791322506874125561)
      ·
        refine ⟨198839093491880155594171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265118791322506874125561 198839093491880155594171)
        ·
          refine ⟨298258640237820233391257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198839093491880155594171 298258640237820233391257)
          ·
            refine ⟨223693980178365175043443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298258640237820233391257 223693980178365175043443)
            ·
              refine ⟨335540970267547762565165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223693980178365175043443 335540970267547762565165)
              ·
                refine ⟨125827863850330410961937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335540970267547762565165 125827863850330410961937)
                ·
                  refine ⟨94370897887747808221453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125827863850330410961937 94370897887747808221453)
                  ·
                    rfl

theorem cell20_206760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_206760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206760 prefixEnd_206760 := by exact prefixLift 206760
  have htrace : WordTrace (prefixWord ++ tailWord_206760) baseStart_206760 baseEnd_206760 := by
    simpa [prefixWord, tailWord_206760, baseEnd_206760] using wordTrace_append hprefix tailTrace_206760
  have hstable : (prefixWord ++ tailWord_206760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206760).length < 2 ^ (prefixWord ++ tailWord_206760).sum := by decide
  have hdescent : baseEnd_206760 < baseStart_206760 := by decide
  rcases family_descends (prefixWord ++ tailWord_206760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206789 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_206789 : Nat := 118140960795 + 206789 * 2 ^ 59
def prefixEnd_206789 : Nat := 4983230072969 + 3 ^ 40 * 206789 * 2
def baseEnd_206789 : Nat := 94384134277952596254667

theorem tailTrace_206789 : CollatzResearch.WordTrace tailWord_206789 prefixEnd_206789 94384134277952596254667 := by
  unfold tailWord_206789
  simp only [CollatzResearch.WordTrace]
  refine ⟨7542214447846244594599421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5028142965230829729732947 7542214447846244594599421)
  ·
    refine ⟨2828330417942341722974783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7542214447846244594599421 2828330417942341722974783)
    ·
      refine ⟨4242495626913512584462175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828330417942341722974783 4242495626913512584462175)
      ·
        refine ⟨6363743440370268876693263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4242495626913512584462175 6363743440370268876693263)
        ·
          refine ⟨9545615160555403315039895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6363743440370268876693263 9545615160555403315039895)
          ·
            refine ⟨14318422740833104972559843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9545615160555403315039895 14318422740833104972559843)
            ·
              refine ⟨21477634111249657458839765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14318422740833104972559843 21477634111249657458839765)
              ·
                refine ⟨503382049482413846691557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21477634111249657458839765 503382049482413846691557)
                ·
                  refine ⟨94384134277952596254667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503382049482413846691557 94384134277952596254667)
                  ·
                    rfl

theorem cell20_206789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_206789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206789 prefixEnd_206789 := by exact prefixLift 206789
  have htrace : WordTrace (prefixWord ++ tailWord_206789) baseStart_206789 baseEnd_206789 := by
    simpa [prefixWord, tailWord_206789, baseEnd_206789] using wordTrace_append hprefix tailTrace_206789
  have hstable : (prefixWord ++ tailWord_206789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206789).length < 2 ^ (prefixWord ++ tailWord_206789).sum := by decide
  have hdescent : baseEnd_206789 < baseStart_206789 := by decide
  rcases family_descends (prefixWord ++ tailWord_206789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206834 : List Nat := [3, 2, 1, 14]
def baseStart_206834 : Nat := 118140960795 + 206834 * 2 ^ 59
def prefixEnd_206834 : Nat := 4983230072969 + 3 ^ 40 * 206834 * 2
def baseEnd_206834 : Nat := 388496598782438023681

theorem tailTrace_206834 : CollatzResearch.WordTrace tailWord_206834 prefixEnd_206834 388496598782438023681 := by
  unfold tailWord_206834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885963933170804319996889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5029237155122144853325037 1885963933170804319996889)
  ·
    refine ⟨1414472949878103239997667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1885963933170804319996889 1414472949878103239997667)
    ·
      refine ⟨2121709424817154859996501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414472949878103239997667 2121709424817154859996501)
      ·
        refine ⟨388496598782438023681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 2121709424817154859996501 388496598782438023681)
        ·
          rfl

theorem cell20_206834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 14].length) (baseStart_206834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206834 prefixEnd_206834 := by exact prefixLift 206834
  have htrace : WordTrace (prefixWord ++ tailWord_206834) baseStart_206834 baseEnd_206834 := by
    simpa [prefixWord, tailWord_206834, baseEnd_206834] using wordTrace_append hprefix tailTrace_206834
  have hstable : (prefixWord ++ tailWord_206834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206834).length < 2 ^ (prefixWord ++ tailWord_206834).sum := by decide
  have hdescent : baseEnd_206834 < baseStart_206834 := by decide
  rcases family_descends (prefixWord ++ tailWord_206834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206888 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 3]
def baseStart_206888 : Nat := 118140960795 + 206888 * 2 ^ 59
def prefixEnd_206888 : Nat := 4983230072969 + 3 ^ 40 * 206888 * 2
def baseEnd_206888 : Nat := 94429320575548251954263

theorem tailTrace_206888 : CollatzResearch.WordTrace tailWord_206888 prefixEnd_206888 94429320575548251954263 := by
  unfold tailWord_206888
  simp only [CollatzResearch.WordTrace]
  refine ⟨3772912637243792251226659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5030550182991723001635545 3772912637243792251226659)
  ·
    refine ⟨5659368955865688376839989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3772912637243792251226659 5659368955865688376839989)
    ·
      refine ⟨530565839612408285328749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5659368955865688376839989 530565839612408285328749)
      ·
        refine ⟨198962189854653106998281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530565839612408285328749 198962189854653106998281)
        ·
          refine ⟨149221642390989830248711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198962189854653106998281 149221642390989830248711)
          ·
            refine ⟨223832463586484745373067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149221642390989830248711 223832463586484745373067)
            ·
              refine ⟨335748695379727118059601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223832463586484745373067 335748695379727118059601)
              ·
                refine ⟨251811521534795338544701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335748695379727118059601 251811521534795338544701)
                ·
                  refine ⟨94429320575548251954263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251811521534795338544701 94429320575548251954263)
                  ·
                    rfl

theorem cell20_206888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_206888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206888 prefixEnd_206888 := by exact prefixLift 206888
  have htrace : WordTrace (prefixWord ++ tailWord_206888) baseStart_206888 baseEnd_206888 := by
    simpa [prefixWord, tailWord_206888, baseEnd_206888] using wordTrace_append hprefix tailTrace_206888
  have hstable : (prefixWord ++ tailWord_206888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206888).length < 2 ^ (prefixWord ++ tailWord_206888).sum := by decide
  have hdescent : baseEnd_206888 < baseStart_206888 := by decide
  rcases family_descends (prefixWord ++ tailWord_206888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206896 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_206896 : Nat := 118140960795 + 206896 * 2 ^ 59
def prefixEnd_206896 : Nat := 4983230072969 + 3 ^ 40 * 206896 * 2
def baseEnd_206896 : Nat := 94432971993535779687563

theorem tailTrace_206896 : CollatzResearch.WordTrace tailWord_206896 prefixEnd_206896 94432971993535779687563 := by
  unfold tailWord_206896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3773058529229300934372271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5030744705639067912496361 3773058529229300934372271)
  ·
    refine ⟨5659587793843951401558407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3773058529229300934372271 5659587793843951401558407)
    ·
      refine ⟨8489381690765927102337611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5659587793843951401558407 8489381690765927102337611)
      ·
        refine ⟨12734072536148890653506417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8489381690765927102337611 12734072536148890653506417)
        ·
          refine ⟨9550554402111667990129813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12734072536148890653506417 9550554402111667990129813)
          ·
            refine ⟨447682237598984437037335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9550554402111667990129813 447682237598984437037335)
            ·
              refine ⟨671523356398476655556003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447682237598984437037335 671523356398476655556003)
              ·
                refine ⟨1007285034597714983334005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671523356398476655556003 1007285034597714983334005)
                ·
                  refine ⟨94432971993535779687563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1007285034597714983334005 94432971993535779687563)
                  ·
                    rfl

theorem cell20_206896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_206896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206896 prefixEnd_206896 := by exact prefixLift 206896
  have htrace : WordTrace (prefixWord ++ tailWord_206896) baseStart_206896 baseEnd_206896 := by
    simpa [prefixWord, tailWord_206896, baseEnd_206896] using wordTrace_append hprefix tailTrace_206896
  have hstable : (prefixWord ++ tailWord_206896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206896).length < 2 ^ (prefixWord ++ tailWord_206896).sum := by decide
  have hdescent : baseEnd_206896 < baseStart_206896 := by decide
  rcases family_descends (prefixWord ++ tailWord_206896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206903 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_206903 : Nat := 118140960795 + 206903 * 2 ^ 59
def prefixEnd_206903 : Nat := 4983230072969 + 3 ^ 40 * 206903 * 2
def baseEnd_206903 : Nat := 94436166984274866454201

theorem tailTrace_206903 : CollatzResearch.WordTrace tailWord_206903 prefixEnd_206903 94436166984274866454201 := by
  unfold tailWord_206903
  simp only [CollatzResearch.WordTrace]
  refine ⟨7546372369433242064249363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5030914912955494709499575 7546372369433242064249363)
  ·
    refine ⟨11319558554149863096374045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7546372369433242064249363 11319558554149863096374045)
    ·
      refine ⟨4244834457806198661140267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11319558554149863096374045 4244834457806198661140267)
      ·
        refine ⟨6367251686709297991710401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4244834457806198661140267 6367251686709297991710401)
        ·
          refine ⟨4775438765031973493782801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6367251686709297991710401 4775438765031973493782801)
          ·
            refine ⟨3581579073773980120337101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4775438765031973493782801 3581579073773980120337101)
            ·
              refine ⟨1343092152665242545126413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3581579073773980120337101 1343092152665242545126413)
              ·
                refine ⟨503659557249465954422405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1343092152665242545126413 503659557249465954422405)
                ·
                  refine ⟨94436166984274866454201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503659557249465954422405 94436166984274866454201)
                  ·
                    rfl

theorem cell20_206903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_206903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206903 prefixEnd_206903 := by exact prefixLift 206903
  have htrace : WordTrace (prefixWord ++ tailWord_206903) baseStart_206903 baseEnd_206903 := by
    simpa [prefixWord, tailWord_206903, baseEnd_206903] using wordTrace_append hprefix tailTrace_206903
  have hstable : (prefixWord ++ tailWord_206903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206903).length < 2 ^ (prefixWord ++ tailWord_206903).sum := by decide
  have hdescent : baseEnd_206903 < baseStart_206903 := by decide
  rcases family_descends (prefixWord ++ tailWord_206903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206948 : List Nat := [2, 3, 1, 1, 2, 1, 10]
def baseStart_206948 : Nat := 118140960795 + 206948 * 2 ^ 59
def prefixEnd_206948 : Nat := 4983230072969 + 3 ^ 40 * 206948 * 2
def baseEnd_206948 : Nat := 10495189578939412217113

theorem tailTrace_206948 : CollatzResearch.WordTrace tailWord_206948 prefixEnd_206948 10495189578939412217113 := by
  unfold tailWord_206948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774006827135107374818749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5032009102846809833091665 3774006827135107374818749)
  ·
    refine ⟨1415252560175665265557031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3774006827135107374818749 1415252560175665265557031)
    ·
      refine ⟨2122878840263497898335547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415252560175665265557031 2122878840263497898335547)
      ·
        refine ⟨3184318260395246847503321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2122878840263497898335547 3184318260395246847503321)
        ·
          refine ⟨2388238695296435135627491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3184318260395246847503321 2388238695296435135627491)
          ·
            refine ⟨3582358042944652703441237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388238695296435135627491 3582358042944652703441237)
            ·
              refine ⟨10495189578939412217113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3582358042944652703441237 10495189578939412217113)
              ·
                rfl

theorem cell20_206948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 10].length) (baseStart_206948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206948 prefixEnd_206948 := by exact prefixLift 206948
  have htrace : WordTrace (prefixWord ++ tailWord_206948) baseStart_206948 baseEnd_206948 := by
    simpa [prefixWord, tailWord_206948, baseEnd_206948] using wordTrace_append hprefix tailTrace_206948
  have hstable : (prefixWord ++ tailWord_206948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206948).length < 2 ^ (prefixWord ++ tailWord_206948).sum := by decide
  have hdescent : baseEnd_206948 < baseStart_206948 := by decide
  rcases family_descends (prefixWord ++ tailWord_206948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206954 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 4]
def baseStart_206954 : Nat := 118140960795 + 206954 * 2 ^ 59
def prefixEnd_206954 : Nat := 4983230072969 + 3 ^ 40 * 206954 * 2
def baseEnd_206954 : Nat := 94459444773945355753993

theorem tailTrace_206954 : CollatzResearch.WordTrace tailWord_206954 prefixEnd_206954 94459444773945355753993 := by
  unfold tailWord_206954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887058123062119443588979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5032154994832318516237277 1887058123062119443588979)
  ·
    refine ⟨2830587184593179165383469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1887058123062119443588979 2830587184593179165383469)
    ·
      refine ⟨1061470194222442187018801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2830587184593179165383469 1061470194222442187018801)
      ·
        refine ⟨796102645666831640264101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1061470194222442187018801 796102645666831640264101)
        ·
          refine ⟨149269246062530932549519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 796102645666831640264101 149269246062530932549519)
          ·
            refine ⟨223903869093796398824279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149269246062530932549519 223903869093796398824279)
            ·
              refine ⟨335855803640694598236419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223903869093796398824279 335855803640694598236419)
              ·
                refine ⟨503783705461041897354629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335855803640694598236419 503783705461041897354629)
                ·
                  refine ⟨94459444773945355753993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503783705461041897354629 94459444773945355753993)
                  ·
                    rfl

theorem cell20_206954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_206954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_206954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_206954 prefixEnd_206954 := by exact prefixLift 206954
  have htrace : WordTrace (prefixWord ++ tailWord_206954) baseStart_206954 baseEnd_206954 := by
    simpa [prefixWord, tailWord_206954, baseEnd_206954] using wordTrace_append hprefix tailTrace_206954
  have hstable : (prefixWord ++ tailWord_206954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206954).length < 2 ^ (prefixWord ++ tailWord_206954).sum := by decide
  have hdescent : baseEnd_206954 < baseStart_206954 := by decide
  rcases family_descends (prefixWord ++ tailWord_206954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207061 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 3]
def baseStart_207061 : Nat := 118140960795 + 207061 * 2 ^ 59
def prefixEnd_207061 : Nat := 4983230072969 + 3 ^ 40 * 207061 * 2
def baseEnd_207061 : Nat := 94508282489528539186889

theorem tailTrace_207061 : CollatzResearch.WordTrace tailWord_207061 prefixEnd_207061 94508282489528539186889 := by
  unfold tailWord_207061
  simp only [CollatzResearch.WordTrace]
  refine ⟨7552135102860835048501037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5034756735240556699000691 7552135102860835048501037)
  ·
    refine ⟨2832050663572813143187889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7552135102860835048501037 2832050663572813143187889)
    ·
      refine ⟨2124037997679609857390917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2832050663572813143187889 2124037997679609857390917)
      ·
        refine ⟨398257124564926848260797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2124037997679609857390917 398257124564926848260797)
        ·
          refine ⟨149346421711847568097799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398257124564926848260797 149346421711847568097799)
          ·
            refine ⟨224019632567771352146699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149346421711847568097799 224019632567771352146699)
            ·
              refine ⟨336029448851657028220049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224019632567771352146699 336029448851657028220049)
              ·
                refine ⟨252022086638742771165037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336029448851657028220049 252022086638742771165037)
                ·
                  refine ⟨94508282489528539186889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252022086638742771165037 94508282489528539186889)
                  ·
                    rfl

theorem cell20_207061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_207061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207061 prefixEnd_207061 := by exact prefixLift 207061
  have htrace : WordTrace (prefixWord ++ tailWord_207061) baseStart_207061 baseEnd_207061 := by
    simpa [prefixWord, tailWord_207061, baseEnd_207061] using wordTrace_append hprefix tailTrace_207061
  have hstable : (prefixWord ++ tailWord_207061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207061).length < 2 ^ (prefixWord ++ tailWord_207061).sum := by decide
  have hdescent : baseEnd_207061 < baseStart_207061 := by decide
  rcases family_descends (prefixWord ++ tailWord_207061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207068 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 4]
def baseStart_207068 : Nat := 118140960795 + 207068 * 2 ^ 59
def prefixEnd_207068 : Nat := 4983230072969 + 3 ^ 40 * 207068 * 2
def baseEnd_207068 : Nat := 94511477480267625953527

theorem tailTrace_207068 : CollatzResearch.WordTrace tailWord_207068 prefixEnd_207068 94511477480267625953527 := by
  unfold tailWord_207068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3776195206917737622002929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5034926942556983496003905 3776195206917737622002929)
  ·
    refine ⟨2832146405188303216502197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3776195206917737622002929 2832146405188303216502197)
    ·
      refine ⟨265513725486403426547081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2832146405188303216502197 265513725486403426547081)
      ·
        refine ⟨199135294114802569910311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265513725486403426547081 199135294114802569910311)
        ·
          refine ⟨298702941172203854865467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199135294114802569910311 298702941172203854865467)
          ·
            refine ⟨448054411758305782298201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298702941172203854865467 448054411758305782298201)
            ·
              refine ⟨336040808818729336723651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448054411758305782298201 336040808818729336723651)
              ·
                refine ⟨504061213228094005085477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336040808818729336723651 504061213228094005085477)
                ·
                  refine ⟨94511477480267625953527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 504061213228094005085477 94511477480267625953527)
                  ·
                    rfl

theorem cell20_207068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_207068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207068 prefixEnd_207068 := by exact prefixLift 207068
  have htrace : WordTrace (prefixWord ++ tailWord_207068) baseStart_207068 baseEnd_207068 := by
    simpa [prefixWord, tailWord_207068, baseEnd_207068] using wordTrace_append hprefix tailTrace_207068
  have hstable : (prefixWord ++ tailWord_207068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207068).length < 2 ^ (prefixWord ++ tailWord_207068).sum := by decide
  have hdescent : baseEnd_207068 < baseStart_207068 := by decide
  rcases family_descends (prefixWord ++ tailWord_207068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207072 : List Nat := [2, 1, 1, 3, 1, 3, 1, 6, 2]
def baseStart_207072 : Nat := 118140960795 + 207072 * 2 ^ 59
def prefixEnd_207072 : Nat := 4983230072969 + 3 ^ 40 * 207072 * 2
def baseEnd_207072 : Nat := 94513303189261389820177

theorem tailTrace_207072 : CollatzResearch.WordTrace tailWord_207072 prefixEnd_207072 94513303189261389820177 := by
  unfold tailWord_207072
  simp only [CollatzResearch.WordTrace]
  refine ⟨3776268152910491963575735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5035024203880655951434313 3776268152910491963575735)
  ·
    refine ⟨5664402229365737945363603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3776268152910491963575735 5664402229365737945363603)
    ·
      refine ⟨8496603344048606918045405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5664402229365737945363603 8496603344048606918045405)
      ·
        refine ⟨3186226254018227594267027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8496603344048606918045405 3186226254018227594267027)
        ·
          refine ⟨4779339381027341391400541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186226254018227594267027 4779339381027341391400541)
          ·
            refine ⟨1792252267885253021775203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4779339381027341391400541 1792252267885253021775203)
            ·
              refine ⟨2688378401827879532662805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792252267885253021775203 2688378401827879532662805)
              ·
                refine ⟨126017737585681853093569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2688378401827879532662805 126017737585681853093569)
                ·
                  refine ⟨94513303189261389820177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126017737585681853093569 94513303189261389820177)
                  ·
                    rfl

theorem cell20_207072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_207072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207072 prefixEnd_207072 := by exact prefixLift 207072
  have htrace : WordTrace (prefixWord ++ tailWord_207072) baseStart_207072 baseEnd_207072 := by
    simpa [prefixWord, tailWord_207072, baseEnd_207072] using wordTrace_append hprefix tailTrace_207072
  have hstable : (prefixWord ++ tailWord_207072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207072).length < 2 ^ (prefixWord ++ tailWord_207072).sum := by decide
  have hdescent : baseEnd_207072 < baseStart_207072 := by decide
  rcases family_descends (prefixWord ++ tailWord_207072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207106 : List Nat := [3, 4, 1, 1, 2, 1, 3, 3, 2]
def baseStart_207106 : Nat := 118140960795 + 207106 * 2 ^ 59
def prefixEnd_207106 : Nat := 4983230072969 + 3 ^ 40 * 207106 * 2
def baseEnd_207106 : Nat := 94528821715708382686705

theorem tailTrace_207106 : CollatzResearch.WordTrace tailWord_207106 prefixEnd_207106 94528821715708382686705 := by
  unfold tailWord_207106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888444096924451933472293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5035850925131871822592781 1888444096924451933472293)
  ·
    refine ⟨354083268173334737526055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1888444096924451933472293 354083268173334737526055)
    ·
      refine ⟨531124902260002106289083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354083268173334737526055 531124902260002106289083)
      ·
        refine ⟨796687353390003159433625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531124902260002106289083 796687353390003159433625)
        ·
          refine ⟨597515515042502369575219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796687353390003159433625 597515515042502369575219)
          ·
            refine ⟨896273272563753554362829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597515515042502369575219 896273272563753554362829)
            ·
              refine ⟨336102477211407582886061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 896273272563753554362829 336102477211407582886061)
              ·
                refine ⟨126038428954277843582273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336102477211407582886061 126038428954277843582273)
                ·
                  refine ⟨94528821715708382686705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126038428954277843582273 94528821715708382686705)
                  ·
                    rfl

theorem cell20_207106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_207106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207106 prefixEnd_207106 := by exact prefixLift 207106
  have htrace : WordTrace (prefixWord ++ tailWord_207106) baseStart_207106 baseEnd_207106 := by
    simpa [prefixWord, tailWord_207106, baseEnd_207106] using wordTrace_append hprefix tailTrace_207106
  have hstable : (prefixWord ++ tailWord_207106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207106).length < 2 ^ (prefixWord ++ tailWord_207106).sum := by decide
  have hdescent : baseEnd_207106 < baseStart_207106 := by decide
  rcases family_descends (prefixWord ++ tailWord_207106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207107 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_207107 : Nat := 118140960795 + 207107 * 2 ^ 59
def prefixEnd_207107 : Nat := 4983230072969 + 3 ^ 40 * 207107 * 2
def baseEnd_207107 : Nat := 94529278142956823653367

theorem tailTrace_207107 : CollatzResearch.WordTrace tailWord_207107 prefixEnd_207107 94529278142956823653367 := by
  unfold tailWord_207107
  simp only [CollatzResearch.WordTrace]
  refine ⟨7553812860694184904675575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5035875240462789936450383 7553812860694184904675575)
  ·
    refine ⟨11330719291041277357013363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7553812860694184904675575 11330719291041277357013363)
    ·
      refine ⟨16996078936561916035520045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11330719291041277357013363 16996078936561916035520045)
      ·
        refine ⟨6373529601210718513320017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16996078936561916035520045 6373529601210718513320017)
        ·
          refine ⟨4780147200908038884990013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6373529601210718513320017 4780147200908038884990013)
          ·
            refine ⟨1792555200340514581871255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4780147200908038884990013 1792555200340514581871255)
            ·
              refine ⟨2688832800510771872806883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792555200340514581871255 2688832800510771872806883)
              ·
                refine ⟨4033249200766157809210325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688832800510771872806883 4033249200766157809210325)
                ·
                  refine ⟨94529278142956823653367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4033249200766157809210325 94529278142956823653367)
                  ·
                    rfl

theorem cell20_207107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_207107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207107 prefixEnd_207107 := by exact prefixLift 207107
  have htrace : WordTrace (prefixWord ++ tailWord_207107) baseStart_207107 baseEnd_207107 := by
    simpa [prefixWord, tailWord_207107, baseEnd_207107] using wordTrace_append hprefix tailTrace_207107
  have hstable : (prefixWord ++ tailWord_207107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207107).length < 2 ^ (prefixWord ++ tailWord_207107).sum := by decide
  have hdescent : baseEnd_207107 < baseStart_207107 := by decide
  rcases family_descends (prefixWord ++ tailWord_207107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207131 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 4]
def baseStart_207131 : Nat := 118140960795 + 207131 * 2 ^ 59
def prefixEnd_207131 : Nat := 4983230072969 + 3 ^ 40 * 207131 * 2
def baseEnd_207131 : Nat := 94540232396919406853269

theorem tailTrace_207131 : CollatzResearch.WordTrace tailWord_207131 prefixEnd_207131 94540232396919406853269 := by
  unfold tailWord_207131
  simp only [CollatzResearch.WordTrace]
  refine ⟨7554688212607237003549247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5036458808404824669032831 7554688212607237003549247)
  ·
    refine ⟨11332032318910855505323871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7554688212607237003549247 11332032318910855505323871)
    ·
      refine ⟨16998048478366283257985807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11332032318910855505323871 16998048478366283257985807)
      ·
        refine ⟨25497072717549424886978711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16998048478366283257985807 25497072717549424886978711)
        ·
          refine ⟨38245609076324137330468067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25497072717549424886978711 38245609076324137330468067)
          ·
            refine ⟨57368413614486205995702101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38245609076324137330468067 57368413614486205995702101)
            ·
              refine ⟨336143048522380113256067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 57368413614486205995702101 336143048522380113256067)
              ·
                refine ⟨504214572783570169884101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336143048522380113256067 504214572783570169884101)
                ·
                  refine ⟨94540232396919406853269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 504214572783570169884101 94540232396919406853269)
                  ·
                    rfl

theorem cell20_207131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_207131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207131 prefixEnd_207131 := by exact prefixLift 207131
  have htrace : WordTrace (prefixWord ++ tailWord_207131) baseStart_207131 baseEnd_207131 := by
    simpa [prefixWord, tailWord_207131, baseEnd_207131] using wordTrace_append hprefix tailTrace_207131
  have hstable : (prefixWord ++ tailWord_207131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207131).length < 2 ^ (prefixWord ++ tailWord_207131).sum := by decide
  have hdescent : baseEnd_207131 < baseStart_207131 := by decide
  rcases family_descends (prefixWord ++ tailWord_207131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207134 : List Nat := [4, 3, 2, 1, 1, 1, 1, 7]
def baseStart_207134 : Nat := 118140960795 + 207134 * 2 ^ 59
def prefixEnd_207134 : Nat := 4983230072969 + 3 ^ 40 * 207134 * 2
def baseEnd_207134 : Nat := 31513867226221576584419

theorem tailTrace_207134 : CollatzResearch.WordTrace tailWord_207134 prefixEnd_207134 31513867226221576584419 := by
  unfold tailWord_207134
  simp only [CollatzResearch.WordTrace]
  refine ⟨944349703949546064488557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5036531754397579010605637 944349703949546064488557)
  ·
    refine ⟨354131138981079774183209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 944349703949546064488557 354131138981079774183209)
    ·
      refine ⟨265598354235809830637407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354131138981079774183209 265598354235809830637407)
      ·
        refine ⟨398397531353714745956111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265598354235809830637407 398397531353714745956111)
        ·
          refine ⟨597596297030572118934167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398397531353714745956111 597596297030572118934167)
          ·
            refine ⟨896394445545858178401251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597596297030572118934167 896394445545858178401251)
            ·
              refine ⟨1344591668318787267601877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896394445545858178401251 1344591668318787267601877)
              ·
                refine ⟨31513867226221576584419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1344591668318787267601877 31513867226221576584419)
                ·
                  rfl

theorem cell20_207134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_207134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207134 prefixEnd_207134 := by exact prefixLift 207134
  have htrace : WordTrace (prefixWord ++ tailWord_207134) baseStart_207134 baseEnd_207134 := by
    simpa [prefixWord, tailWord_207134, baseEnd_207134] using wordTrace_append hprefix tailTrace_207134
  have hstable : (prefixWord ++ tailWord_207134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207134).length < 2 ^ (prefixWord ++ tailWord_207134).sum := by decide
  have hdescent : baseEnd_207134 < baseStart_207134 := by decide
  rcases family_descends (prefixWord ++ tailWord_207134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207141 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 3]
def baseStart_207141 : Nat := 118140960795 + 207141 * 2 ^ 59
def prefixEnd_207141 : Nat := 4983230072969 + 3 ^ 40 * 207141 * 2
def baseEnd_207141 : Nat := 94544796669403816519895

theorem tailTrace_207141 : CollatzResearch.WordTrace tailWord_207141 prefixEnd_207141 94544796669403816519895 := by
  unfold tailWord_207141
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555052942571008711413277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5036701961714005807608851 7555052942571008711413277)
  ·
    refine ⟨2833144853464128266779979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7555052942571008711413277 2833144853464128266779979)
    ·
      refine ⟨4249717280196192400169969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2833144853464128266779979 4249717280196192400169969)
      ·
        refine ⟨3187287960147144300127477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4249717280196192400169969 3187287960147144300127477)
        ·
          refine ⟨298808246263794778136951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3187287960147144300127477 298808246263794778136951)
          ·
            refine ⟨448212369395692167205427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298808246263794778136951 448212369395692167205427)
            ·
              refine ⟨672318554093538250808141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448212369395692167205427 672318554093538250808141)
              ·
                refine ⟨252119457785076844053053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 672318554093538250808141 252119457785076844053053)
                ·
                  refine ⟨94544796669403816519895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252119457785076844053053 94544796669403816519895)
                  ·
                    rfl

theorem cell20_207141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_207141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207141 prefixEnd_207141 := by exact prefixLift 207141
  have htrace : WordTrace (prefixWord ++ tailWord_207141) baseStart_207141 baseEnd_207141 := by
    simpa [prefixWord, tailWord_207141, baseEnd_207141] using wordTrace_append hprefix tailTrace_207141
  have hstable : (prefixWord ++ tailWord_207141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207141).length < 2 ^ (prefixWord ++ tailWord_207141).sum := by decide
  have hdescent : baseEnd_207141 < baseStart_207141 := by decide
  rcases family_descends (prefixWord ++ tailWord_207141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207172 : List Nat := [2, 3, 4, 1, 3, 7]
def baseStart_207172 : Nat := 118140960795 + 207172 * 2 ^ 59
def prefixEnd_207172 : Nat := 4983230072969 + 3 ^ 40 * 207172 * 2
def baseEnd_207172 : Nat := 3502183182003906906905

theorem tailTrace_207172 : CollatzResearch.WordTrace tailWord_207172 prefixEnd_207172 3502183182003906906905 := by
  unfold tailWord_207172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778091802729350502895885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5037455736972467337194513 3778091802729350502895885)
  ·
    refine ⟨1416784426023506438585957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3778091802729350502895885 1416784426023506438585957)
    ·
      refine ⟨265647079879407457234867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1416784426023506438585957 265647079879407457234867)
      ·
        refine ⟨398470619819111185852301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265647079879407457234867 398470619819111185852301)
        ·
          refine ⟨149426482432166694694613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398470619819111185852301 149426482432166694694613)
          ·
            refine ⟨3502183182003906906905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 149426482432166694694613 3502183182003906906905)
            ·
              rfl

theorem cell20_207172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 7].length) (baseStart_207172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207172 prefixEnd_207172 := by exact prefixLift 207172
  have htrace : WordTrace (prefixWord ++ tailWord_207172) baseStart_207172 baseEnd_207172 := by
    simpa [prefixWord, tailWord_207172, baseEnd_207172] using wordTrace_append hprefix tailTrace_207172
  have hstable : (prefixWord ++ tailWord_207172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207172).length < 2 ^ (prefixWord ++ tailWord_207172).sum := by decide
  have hdescent : baseEnd_207172 < baseStart_207172 := by decide
  rcases family_descends (prefixWord ++ tailWord_207172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207207 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_207207 : Nat := 118140960795 + 207207 * 2 ^ 59
def prefixEnd_207207 : Nat := 4983230072969 + 3 ^ 40 * 207207 * 2
def baseEnd_207207 : Nat := 94574920867800920319625

theorem tailTrace_207207 : CollatzResearch.WordTrace tailWord_207207 prefixEnd_207207 94574920867800920319625 := by
  unfold tailWord_207207
  simp only [CollatzResearch.WordTrace]
  refine ⟨7557460160331901983315875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5038306773554601322210583 7557460160331901983315875)
  ·
    refine ⟨11336190240497852974973813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7557460160331901983315875 11336190240497852974973813)
    ·
      refine ⟨1062767835046673716403795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11336190240497852974973813 1062767835046673716403795)
      ·
        refine ⟨1594151752570010574605693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062767835046673716403795 1594151752570010574605693)
        ·
          refine ⟨597806907213753965477135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1594151752570010574605693 597806907213753965477135)
          ·
            refine ⟨896710360820630948215703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597806907213753965477135 896710360820630948215703)
            ·
              refine ⟨1345065541230946422323555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896710360820630948215703 1345065541230946422323555)
              ·
                refine ⟨2017598311846419633485333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345065541230946422323555 2017598311846419633485333)
                ·
                  refine ⟨94574920867800920319625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2017598311846419633485333 94574920867800920319625)
                  ·
                    rfl

theorem cell20_207207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_207207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207207 prefixEnd_207207 := by exact prefixLift 207207
  have htrace : WordTrace (prefixWord ++ tailWord_207207) baseStart_207207 baseEnd_207207 := by
    simpa [prefixWord, tailWord_207207, baseEnd_207207] using wordTrace_append hprefix tailTrace_207207
  have hstable : (prefixWord ++ tailWord_207207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207207).length < 2 ^ (prefixWord ++ tailWord_207207).sum := by decide
  have hdescent : baseEnd_207207 < baseStart_207207 := by decide
  rcases family_descends (prefixWord ++ tailWord_207207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207210 : List Nat := [3, 1, 3, 3, 1, 2, 3, 4]
def baseStart_207210 : Nat := 118140960795 + 207210 * 2 ^ 59
def prefixEnd_207210 : Nat := 4983230072969 + 3 ^ 40 * 207210 * 2
def baseEnd_207210 : Nat := 31525430049848747739871

theorem tailTrace_207210 : CollatzResearch.WordTrace tailWord_207210 prefixEnd_207210 31525430049848747739871 := by
  unfold tailWord_207210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889392394830258373918771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5038379719547355663783389 1889392394830258373918771)
  ·
    refine ⟨2834088592245387560878157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1889392394830258373918771 2834088592245387560878157)
    ·
      refine ⟨1062783222092020335329309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2834088592245387560878157 1062783222092020335329309)
      ·
        refine ⟨398543708284507625748491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1062783222092020335329309 398543708284507625748491)
        ·
          refine ⟨597815562426761438622737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398543708284507625748491 597815562426761438622737)
          ·
            refine ⟨448361671820071078967053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597815562426761438622737 448361671820071078967053)
            ·
              refine ⟨168135626932526654612645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 448361671820071078967053 168135626932526654612645)
              ·
                refine ⟨31525430049848747739871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168135626932526654612645 31525430049848747739871)
                ·
                  rfl

theorem cell20_207210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_207210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207210 prefixEnd_207210 := by exact prefixLift 207210
  have htrace : WordTrace (prefixWord ++ tailWord_207210) baseStart_207210 baseEnd_207210 := by
    simpa [prefixWord, tailWord_207210, baseEnd_207210] using wordTrace_append hprefix tailTrace_207210
  have hstable : (prefixWord ++ tailWord_207210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207210).length < 2 ^ (prefixWord ++ tailWord_207210).sum := by decide
  have hdescent : baseEnd_207210 < baseStart_207210 := by decide
  rcases family_descends (prefixWord ++ tailWord_207210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207234 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_207234 : Nat := 118140960795 + 207234 * 2 ^ 59
def prefixEnd_207234 : Nat := 4983230072969 + 3 ^ 40 * 207234 * 2
def baseEnd_207234 : Nat := 94587244403508826419515

theorem tailTrace_207234 : CollatzResearch.WordTrace tailWord_207234 prefixEnd_207234 94587244403508826419515 := by
  unfold tailWord_207234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889611232808521398637189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5038963287489390396365837 1889611232808521398637189)
  ·
    refine ⟨354302106151597762244473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1889611232808521398637189 354302106151597762244473)
    ·
      refine ⟨265726579613698321683355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354302106151597762244473 265726579613698321683355)
      ·
        refine ⟨398589869420547482525033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265726579613698321683355 398589869420547482525033)
        ·
          refine ⟨298942402065410611893775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398589869420547482525033 298942402065410611893775)
          ·
            refine ⟨448413603098115917840663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298942402065410611893775 448413603098115917840663)
            ·
              refine ⟨672620404647173876760995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448413603098115917840663 672620404647173876760995)
              ·
                refine ⟨1008930606970760815141493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672620404647173876760995 1008930606970760815141493)
                ·
                  refine ⟨94587244403508826419515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1008930606970760815141493 94587244403508826419515)
                  ·
                    rfl

theorem cell20_207234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_207234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207234 prefixEnd_207234 := by exact prefixLift 207234
  have htrace : WordTrace (prefixWord ++ tailWord_207234) baseStart_207234 baseEnd_207234 := by
    simpa [prefixWord, tailWord_207234, baseEnd_207234] using wordTrace_append hprefix tailTrace_207234
  have hstable : (prefixWord ++ tailWord_207234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207234).length < 2 ^ (prefixWord ++ tailWord_207234).sum := by decide
  have hdescent : baseEnd_207234 < baseStart_207234 := by decide
  rcases family_descends (prefixWord ++ tailWord_207234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207265 : List Nat := [1, 2, 3, 5, 1, 2, 2, 4]
def baseStart_207265 : Nat := 118140960795 + 207265 * 2 ^ 59
def prefixEnd_207265 : Nat := 4983230072969 + 3 ^ 40 * 207265 * 2
def baseEnd_207265 : Nat := 31533797882736832128685

theorem tailTrace_207265 : CollatzResearch.WordTrace tailWord_207265 prefixEnd_207265 31533797882736832128685 := by
  unfold tailWord_207265
  simp only [CollatzResearch.WordTrace]
  refine ⟨7559575594121777888927249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5039717062747851925951499 7559575594121777888927249)
  ·
    refine ⟨5669681695591333416695437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7559575594121777888927249 5669681695591333416695437)
    ·
      refine ⟨2126130635846750031260789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5669681695591333416695437 2126130635846750031260789)
      ·
        refine ⟨199324747110632815430699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2126130635846750031260789 199324747110632815430699)
        ·
          refine ⟨298987120665949223146049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199324747110632815430699 298987120665949223146049)
          ·
            refine ⟨224240340499461917359537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298987120665949223146049 224240340499461917359537)
            ·
              refine ⟨168180255374596438019653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224240340499461917359537 168180255374596438019653)
              ·
                refine ⟨31533797882736832128685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168180255374596438019653 31533797882736832128685)
                ·
                  rfl

theorem cell20_207265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 4].length) (baseStart_207265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207265 prefixEnd_207265 := by exact prefixLift 207265
  have htrace : WordTrace (prefixWord ++ tailWord_207265) baseStart_207265 baseEnd_207265 := by
    simpa [prefixWord, tailWord_207265, baseEnd_207265] using wordTrace_append hprefix tailTrace_207265
  have hstable : (prefixWord ++ tailWord_207265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207265).length < 2 ^ (prefixWord ++ tailWord_207265).sum := by decide
  have hdescent : baseEnd_207265 < baseStart_207265 := by decide
  rcases family_descends (prefixWord ++ tailWord_207265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207352 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 3]
def baseStart_207352 : Nat := 118140960795 + 207352 * 2 ^ 59
def prefixEnd_207352 : Nat := 4983230072969 + 3 ^ 40 * 207352 * 2
def baseEnd_207352 : Nat := 94641102818824860485699

theorem tailTrace_207352 : CollatzResearch.WordTrace tailWord_207352 prefixEnd_207352 94641102818824860485699 := by
  unfold tailWord_207352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781374372403295873672155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5041832496537727831562873 3781374372403295873672155)
  ·
    refine ⟨5672061558604943810508233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3781374372403295873672155 5672061558604943810508233)
    ·
      refine ⟨4254046168953707857881175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5672061558604943810508233 4254046168953707857881175)
      ·
        refine ⟨6381069253430561786821763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254046168953707857881175 6381069253430561786821763)
        ·
          refine ⟨9571603880145842680232645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6381069253430561786821763 9571603880145842680232645)
          ·
            refine ⟨1794675727527345502543621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9571603880145842680232645 1794675727527345502543621)
            ·
              refine ⟨336501698911377281726929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1794675727527345502543621 336501698911377281726929)
              ·
                refine ⟨252376274183532961295197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336501698911377281726929 252376274183532961295197)
                ·
                  refine ⟨94641102818824860485699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252376274183532961295197 94641102818824860485699)
                  ·
                    rfl

theorem cell20_207352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_207352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207352 prefixEnd_207352 := by exact prefixLift 207352
  have htrace : WordTrace (prefixWord ++ tailWord_207352) baseStart_207352 baseEnd_207352 := by
    simpa [prefixWord, tailWord_207352, baseEnd_207352] using wordTrace_append hprefix tailTrace_207352
  have hstable : (prefixWord ++ tailWord_207352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207352).length < 2 ^ (prefixWord ++ tailWord_207352).sum := by decide
  have hdescent : baseEnd_207352 < baseStart_207352 := by decide
  rcases family_descends (prefixWord ++ tailWord_207352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207411 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_207411 : Nat := 118140960795 + 207411 * 2 ^ 59
def prefixEnd_207411 : Nat := 4983230072969 + 3 ^ 40 * 207411 * 2
def baseEnd_207411 : Nat := 94668032026482877518791

theorem tailTrace_207411 : CollatzResearch.WordTrace tailWord_207411 prefixEnd_207411 94668032026482877518791 := by
  unfold tailWord_207411
  simp only [CollatzResearch.WordTrace]
  refine ⟨7564900651592844823742087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5043267101061896549161391 7564900651592844823742087)
  ·
    refine ⟨11347350977389267235613131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7564900651592844823742087 11347350977389267235613131)
    ·
      refine ⟨17021026466083900853419697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11347350977389267235613131 17021026466083900853419697)
      ·
        refine ⟨12765769849562925640064773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17021026466083900853419697 12765769849562925640064773)
        ·
          refine ⟨2393581846793048557512145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12765769849562925640064773 2393581846793048557512145)
          ·
            refine ⟨1795186385094786418134109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2393581846793048557512145 1795186385094786418134109)
            ·
              refine ⟨673194894410544906800291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1795186385094786418134109 673194894410544906800291)
              ·
                refine ⟨1009792341615817360200437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673194894410544906800291 1009792341615817360200437)
                ·
                  refine ⟨94668032026482877518791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1009792341615817360200437 94668032026482877518791)
                  ·
                    rfl

theorem cell20_207411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_207411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207411 prefixEnd_207411 := by exact prefixLift 207411
  have htrace : WordTrace (prefixWord ++ tailWord_207411) baseStart_207411 baseEnd_207411 := by
    simpa [prefixWord, tailWord_207411, baseEnd_207411] using wordTrace_append hprefix tailTrace_207411
  have hstable : (prefixWord ++ tailWord_207411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207411).length < 2 ^ (prefixWord ++ tailWord_207411).sum := by decide
  have hdescent : baseEnd_207411 < baseStart_207411 := by decide
  rcases family_descends (prefixWord ++ tailWord_207411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207414 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_207414 : Nat := 118140960795 + 207414 * 2 ^ 59
def prefixEnd_207414 : Nat := 4983230072969 + 3 ^ 40 * 207414 * 2
def baseEnd_207414 : Nat := 94669401308228200418779

theorem tailTrace_207414 : CollatzResearch.WordTrace tailWord_207414 prefixEnd_207414 94669401308228200418779 := by
  unfold tailWord_207414
  simp only [CollatzResearch.WordTrace]
  refine ⟨472813129411373521006331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5043340047054650890734197 472813129411373521006331)
  ·
    refine ⟨709219694117060281509497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 472813129411373521006331 709219694117060281509497)
    ·
      refine ⟨531914770587795211132123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 709219694117060281509497 531914770587795211132123)
      ·
        refine ⟨797872155881692816698185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531914770587795211132123 797872155881692816698185)
        ·
          refine ⟨598404116911269612523639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797872155881692816698185 598404116911269612523639)
          ·
            refine ⟨897606175366904418785459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598404116911269612523639 897606175366904418785459)
            ·
              refine ⟨1346409263050356628178189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897606175366904418785459 1346409263050356628178189)
              ·
                refine ⟨504903473643883735566821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346409263050356628178189 504903473643883735566821)
                ·
                  refine ⟨94669401308228200418779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 504903473643883735566821 94669401308228200418779)
                  ·
                    rfl

theorem cell20_207414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_207414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207414 prefixEnd_207414 := by exact prefixLift 207414
  have htrace : WordTrace (prefixWord ++ tailWord_207414) baseStart_207414 baseEnd_207414 := by
    simpa [prefixWord, tailWord_207414, baseEnd_207414] using wordTrace_append hprefix tailTrace_207414
  have hstable : (prefixWord ++ tailWord_207414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207414).length < 2 ^ (prefixWord ++ tailWord_207414).sum := by decide
  have hdescent : baseEnd_207414 < baseStart_207414 := by decide
  rcases family_descends (prefixWord ++ tailWord_207414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207442 : List Nat := [3, 2, 2, 1, 2, 1, 3, 6]
def baseStart_207442 : Nat := 118140960795 + 207442 * 2 ^ 59
def prefixEnd_207442 : Nat := 4983230072969 + 3 ^ 40 * 207442 * 2
def baseEnd_207442 : Nat := 31560727090394849161777

theorem tailTrace_207442 : CollatzResearch.WordTrace tailWord_207442 prefixEnd_207442 31560727090394849161777 := by
  unfold tailWord_207442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891507828620134279530145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5044020876320358078747053 1891507828620134279530145)
  ·
    refine ⟨1418630871465100709647609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1891507828620134279530145 1418630871465100709647609)
    ·
      refine ⟨1063973153598825532235707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1418630871465100709647609 1063973153598825532235707)
      ·
        refine ⟨1595959730398238298353561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063973153598825532235707 1595959730398238298353561)
        ·
          refine ⟨1196969797798678723765171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1595959730398238298353561 1196969797798678723765171)
          ·
            refine ⟨1795454696698018085647757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196969797798678723765171 1795454696698018085647757)
            ·
              refine ⟨673295511261756782117909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1795454696698018085647757 673295511261756782117909)
              ·
                refine ⟨31560727090394849161777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 673295511261756782117909 31560727090394849161777)
                ·
                  rfl

theorem cell20_207442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_207442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207442 prefixEnd_207442 := by exact prefixLift 207442
  have htrace : WordTrace (prefixWord ++ tailWord_207442) baseStart_207442 baseEnd_207442 := by
    simpa [prefixWord, tailWord_207442, baseEnd_207442] using wordTrace_append hprefix tailTrace_207442
  have hstable : (prefixWord ++ tailWord_207442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207442).length < 2 ^ (prefixWord ++ tailWord_207442).sum := by decide
  have hdescent : baseEnd_207442 < baseStart_207442 := by decide
  rcases family_descends (prefixWord ++ tailWord_207442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207456 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_207456 : Nat := 118140960795 + 207456 * 2 ^ 59
def prefixEnd_207456 : Nat := 4983230072969 + 3 ^ 40 * 207456 * 2
def baseEnd_207456 : Nat := 94688571252662721018607

theorem tailTrace_207456 : CollatzResearch.WordTrace tailWord_207456 prefixEnd_207456 94688571252662721018607 := by
  unfold tailWord_207456
  simp only [CollatzResearch.WordTrace]
  refine ⟨3783270968214908754565111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5044361290953211672753481 3783270968214908754565111)
  ·
    refine ⟨5674906452322363131847667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3783270968214908754565111 5674906452322363131847667)
    ·
      refine ⟨8512359678483544697771501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5674906452322363131847667 8512359678483544697771501)
      ·
        refine ⟨3192134879431329261664313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8512359678483544697771501 3192134879431329261664313)
        ·
          refine ⟨2394101159573496946248235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3192134879431329261664313 2394101159573496946248235)
          ·
            refine ⟨3591151739360245419372353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394101159573496946248235 3591151739360245419372353)
            ·
              refine ⟨2693363804520184064529265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3591151739360245419372353 2693363804520184064529265)
              ·
                refine ⟨2020022853390138048396949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2693363804520184064529265 2020022853390138048396949)
                ·
                  refine ⟨94688571252662721018607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2020022853390138048396949 94688571252662721018607)
                  ·
                    rfl

theorem cell20_207456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_207456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207456 prefixEnd_207456 := by exact prefixLift 207456
  have htrace : WordTrace (prefixWord ++ tailWord_207456) baseStart_207456 baseEnd_207456 := by
    simpa [prefixWord, tailWord_207456, baseEnd_207456] using wordTrace_append hprefix tailTrace_207456
  have hstable : (prefixWord ++ tailWord_207456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207456).length < 2 ^ (prefixWord ++ tailWord_207456).sum := by decide
  have hdescent : baseEnd_207456 < baseStart_207456 := by decide
  rcases family_descends (prefixWord ++ tailWord_207456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207466 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_207466 : Nat := 118140960795 + 207466 * 2 ^ 59
def prefixEnd_207466 : Nat := 4983230072969 + 3 ^ 40 * 207466 * 2
def baseEnd_207466 : Nat := 94693135525147130685233

theorem tailTrace_207466 : CollatzResearch.WordTrace tailWord_207466 prefixEnd_207466 94693135525147130685233 := by
  unfold tailWord_207466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891726666598397304248563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5044604444262392811329501 1891726666598397304248563)
  ·
    refine ⟨2837589999897595956372845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1891726666598397304248563 2837589999897595956372845)
    ·
      refine ⟨1064096249961598483639817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2837589999897595956372845 1064096249961598483639817)
      ·
        refine ⟨798072187471198862729863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064096249961598483639817 798072187471198862729863)
        ·
          refine ⟨1197108281206798294094795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798072187471198862729863 1197108281206798294094795)
          ·
            refine ⟨1795662421810197441142193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197108281206798294094795 1795662421810197441142193)
            ·
              refine ⟨1346746816357648080856645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795662421810197441142193 1346746816357648080856645)
              ·
                refine ⟨252515028067059015160621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1346746816357648080856645 252515028067059015160621)
                ·
                  refine ⟨94693135525147130685233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252515028067059015160621 94693135525147130685233)
                  ·
                    rfl

theorem cell20_207466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_207466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207466 prefixEnd_207466 := by exact prefixLift 207466
  have htrace : WordTrace (prefixWord ++ tailWord_207466) baseStart_207466 baseEnd_207466 := by
    simpa [prefixWord, tailWord_207466, baseEnd_207466] using wordTrace_append hprefix tailTrace_207466
  have hstable : (prefixWord ++ tailWord_207466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207466).length < 2 ^ (prefixWord ++ tailWord_207466).sum := by decide
  have hdescent : baseEnd_207466 < baseStart_207466 := by decide
  rcases family_descends (prefixWord ++ tailWord_207466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207521 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 3]
def baseStart_207521 : Nat := 118140960795 + 207521 * 2 ^ 59
def prefixEnd_207521 : Nat := 4983230072969 + 3 ^ 40 * 207521 * 2
def baseEnd_207521 : Nat := 94718239023811383851675

theorem tailTrace_207521 : CollatzResearch.WordTrace tailWord_207521 prefixEnd_207521 94718239023811383851675 := by
  unfold tailWord_207521
  simp only [CollatzResearch.WordTrace]
  refine ⟨7568912681194333610246417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5045941787462889073497611 7568912681194333610246417)
  ·
    refine ⟨5676684510895750207684813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7568912681194333610246417 5676684510895750207684813)
    ·
      refine ⟨2128756691585906327881805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5676684510895750207684813 2128756691585906327881805)
      ·
        refine ⟨798283759344714872955677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2128756691585906327881805 798283759344714872955677)
        ·
          refine ⟨299356409754268077358379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 798283759344714872955677 299356409754268077358379)
          ·
            refine ⟨449034614631402116037569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299356409754268077358379 449034614631402116037569)
            ·
              refine ⟨336775960973551587028177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449034614631402116037569 336775960973551587028177)
              ·
                refine ⟨252581970730163690271133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336775960973551587028177 252581970730163690271133)
                ·
                  refine ⟨94718239023811383851675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252581970730163690271133 94718239023811383851675)
                  ·
                    rfl

theorem cell20_207521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_207521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207521 prefixEnd_207521 := by exact prefixLift 207521
  have htrace : WordTrace (prefixWord ++ tailWord_207521) baseStart_207521 baseEnd_207521 := by
    simpa [prefixWord, tailWord_207521, baseEnd_207521] using wordTrace_append hprefix tailTrace_207521
  have hstable : (prefixWord ++ tailWord_207521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207521).length < 2 ^ (prefixWord ++ tailWord_207521).sum := by decide
  have hdescent : baseEnd_207521 < baseStart_207521 := by decide
  rcases family_descends (prefixWord ++ tailWord_207521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207549 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 4]
def baseStart_207549 : Nat := 118140960795 + 207549 * 2 ^ 59
def prefixEnd_207549 : Nat := 4983230072969 + 3 ^ 40 * 207549 * 2
def baseEnd_207549 : Nat := 94731018986767730918227

theorem tailTrace_207549 : CollatzResearch.WordTrace tailWord_207549 prefixEnd_207549 94731018986767730918227 := by
  unfold tailWord_207549
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569933925092894392265701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5046622616728596261510467 7569933925092894392265701)
  ·
    refine ⟨1419362610954917698549819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7569933925092894392265701 1419362610954917698549819)
    ·
      refine ⟨2129043916432376547824729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1419362610954917698549819 2129043916432376547824729)
      ·
        refine ⟨1596782937324282410868547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2129043916432376547824729 1596782937324282410868547)
        ·
          refine ⟨2395174405986423616302821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596782937324282410868547 2395174405986423616302821)
          ·
            refine ⟨449095201122454428056779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2395174405986423616302821 449095201122454428056779)
            ·
              refine ⟨673642801683681642085169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449095201122454428056779 673642801683681642085169)
              ·
                refine ⟨505232101262761231563877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673642801683681642085169 505232101262761231563877)
                ·
                  refine ⟨94731018986767730918227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 505232101262761231563877 94731018986767730918227)
                  ·
                    rfl

theorem cell20_207549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_207549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207549 prefixEnd_207549 := by exact prefixLift 207549
  have htrace : WordTrace (prefixWord ++ tailWord_207549) baseStart_207549 baseEnd_207549 := by
    simpa [prefixWord, tailWord_207549, baseEnd_207549] using wordTrace_append hprefix tailTrace_207549
  have hstable : (prefixWord ++ tailWord_207549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207549).length < 2 ^ (prefixWord ++ tailWord_207549).sum := by decide
  have hdescent : baseEnd_207549 < baseStart_207549 := by decide
  rcases family_descends (prefixWord ++ tailWord_207549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207566 : List Nat := [4, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_207566 : Nat := 118140960795 + 207566 * 2 ^ 59
def prefixEnd_207566 : Nat := 4983230072969 + 3 ^ 40 * 207566 * 2
def baseEnd_207566 : Nat := 94738778249991227351491

theorem tailTrace_207566 : CollatzResearch.WordTrace tailWord_207566 prefixEnd_207566 94738778249991227351491 := by
  unfold tailWord_207566
  simp only [CollatzResearch.WordTrace]
  refine ⟨946319245753913286954319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5047035977354204197089701 946319245753913286954319)
  ·
    refine ⟨1419478868630869930431479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 946319245753913286954319 1419478868630869930431479)
    ·
      refine ⟨2129218302946304895647219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1419478868630869930431479 2129218302946304895647219)
      ·
        refine ⟨3193827454419457343470829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129218302946304895647219 3193827454419457343470829)
        ·
          refine ⟨1197685295407296503801561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3193827454419457343470829 1197685295407296503801561)
          ·
            refine ⟨898263971555472377851171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197685295407296503801561 898263971555472377851171)
            ·
              refine ⟨1347395957333208566776757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898263971555472377851171 1347395957333208566776757)
              ·
                refine ⟨126318370999988303135321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1347395957333208566776757 126318370999988303135321)
                ·
                  refine ⟨94738778249991227351491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126318370999988303135321 94738778249991227351491)
                  ·
                    rfl

theorem cell20_207566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_207566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207566 prefixEnd_207566 := by exact prefixLift 207566
  have htrace : WordTrace (prefixWord ++ tailWord_207566) baseStart_207566 baseEnd_207566 := by
    simpa [prefixWord, tailWord_207566, baseEnd_207566] using wordTrace_append hprefix tailTrace_207566
  have hstable : (prefixWord ++ tailWord_207566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207566).length < 2 ^ (prefixWord ++ tailWord_207566).sum := by decide
  have hdescent : baseEnd_207566 < baseStart_207566 := by decide
  rcases family_descends (prefixWord ++ tailWord_207566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
