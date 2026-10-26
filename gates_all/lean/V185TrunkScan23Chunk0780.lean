import V185TrunkScan23Chunk0779

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4613830 : List Nat := [6, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_4613830 : Nat := 118140960795 + 4613830 * 2 ^ 59
def prefixEnd_4613830 : Nat := 4983230072969 + 3 ^ 40 * 4613830 * 2
def baseEnd_4613830 : Nat := 2369112448133788602606389

theorem tailTrace_4613830 : CollatzResearch.WordTrace tailWord_4613830 prefixEnd_4613830 2369112448133788602606389 := by
  unfold tailWord_4613830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5258756402340292633589467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 112186803249926242849908629 5258756402340292633589467)
  ·
    refine ⟨7888134603510438950384201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5258756402340292633589467 7888134603510438950384201)
    ·
      refine ⟨5916100952632829212788151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7888134603510438950384201 5916100952632829212788151)
      ·
        refine ⟨8874151428949243819182227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5916100952632829212788151 8874151428949243819182227)
        ·
          refine ⟨13311227143423865728773341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8874151428949243819182227 13311227143423865728773341)
          ·
            refine ⟨4991710178783949648290003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13311227143423865728773341 4991710178783949648290003)
            ·
              refine ⟨7487565268175924472435005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4991710178783949648290003 7487565268175924472435005)
              ·
                refine ⟨2807836975565971677163127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7487565268175924472435005 2807836975565971677163127)
                ·
                  refine ⟨4211755463348957515744691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807836975565971677163127 4211755463348957515744691)
                  ·
                    refine ⟨6317633195023436273617037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4211755463348957515744691 6317633195023436273617037)
                    ·
                      refine ⟨2369112448133788602606389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6317633195023436273617037 2369112448133788602606389)
                      ·
                        rfl

theorem cell23_4613830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_4613830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613830 prefixEnd_4613830 := by exact prefixLift 4613830
  have htrace : WordTrace (prefixWord ++ tailWord_4613830) baseStart_4613830 baseEnd_4613830 := by
    simpa [prefixWord, tailWord_4613830, baseEnd_4613830] using wordTrace_append hprefix tailTrace_4613830
  have hstable : (prefixWord ++ tailWord_4613830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613830).length < 2 ^ (prefixWord ++ tailWord_4613830).sum := by decide
  have hdescent : baseEnd_4613830 < baseStart_4613830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613848 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_4613848 : Nat := 118140960795 + 4613848 * 2 ^ 59
def prefixEnd_4613848 : Nat := 4983230072969 + 3 ^ 40 * 4613848 * 2
def baseEnd_4613848 : Nat := 2369121690785569532181305

theorem tailTrace_4613848 : CollatzResearch.WordTrace tailWord_4613848 prefixEnd_4613848 2369121690785569532181305 := by
  unfold tailWord_4613848
  simp only [CollatzResearch.WordTrace]
  refine ⟨84140430694412076674509099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112187240925882768899345465 84140430694412076674509099)
  ·
    refine ⟨126210646041618115011763649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84140430694412076674509099 126210646041618115011763649)
    ·
      refine ⟨94657984531213586258822737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126210646041618115011763649 94657984531213586258822737)
      ·
        refine ⟨70993488398410189694117053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94657984531213586258822737 70993488398410189694117053)
        ·
          refine ⟨26622558149403821135293895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70993488398410189694117053 26622558149403821135293895)
          ·
            refine ⟨39933837224105731702940843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26622558149403821135293895 39933837224105731702940843)
            ·
              refine ⟨59900755836158597554411265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39933837224105731702940843 59900755836158597554411265)
              ·
                refine ⟨44925566877118948165808449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59900755836158597554411265 44925566877118948165808449)
                ·
                  refine ⟨33694175157839211124356337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44925566877118948165808449 33694175157839211124356337)
                  ·
                    refine ⟨25270631368379408343267253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33694175157839211124356337 25270631368379408343267253)
                    ·
                      refine ⟨2369121690785569532181305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25270631368379408343267253 2369121690785569532181305)
                      ·
                        rfl

theorem cell23_4613848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_4613848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613848 prefixEnd_4613848 := by exact prefixLift 4613848
  have htrace : WordTrace (prefixWord ++ tailWord_4613848) baseStart_4613848 baseEnd_4613848 := by
    simpa [prefixWord, tailWord_4613848, baseEnd_4613848] using wordTrace_append hprefix tailTrace_4613848
  have hstable : (prefixWord ++ tailWord_4613848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613848).length < 2 ^ (prefixWord ++ tailWord_4613848).sum := by decide
  have hdescent : baseEnd_4613848 < baseStart_4613848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613853 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4613853 : Nat := 118140960795 + 4613853 * 2 ^ 59
def prefixEnd_4613853 : Nat := 4983230072969 + 3 ^ 40 * 4613853 * 2
def baseEnd_4613853 : Nat := 2369124258188842012618783

theorem tailTrace_4613853 : CollatzResearch.WordTrace tailWord_4613853 prefixEnd_4613853 2369124258188842012618783 := by
  unfold tailWord_4613853
  simp only [CollatzResearch.WordTrace]
  refine ⟨168281043753806039202950213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112187362502537359468633475 168281043753806039202950213)
  ·
    refine ⟨31552695703838632350553165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168281043753806039202950213 31552695703838632350553165)
    ·
      refine ⟨11832260888939487131457437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31552695703838632350553165 11832260888939487131457437)
      ·
        refine ⟨4437097833352307674296539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11832260888939487131457437 4437097833352307674296539)
        ·
          refine ⟨6655646750028461511444809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4437097833352307674296539 6655646750028461511444809)
          ·
            refine ⟨4991735062521346133583607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6655646750028461511444809 4991735062521346133583607)
            ·
              refine ⟨7487602593782019200375411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4991735062521346133583607 7487602593782019200375411)
              ·
                refine ⟨11231403890673028800563117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7487602593782019200375411 11231403890673028800563117)
                ·
                  refine ⟨4211776459002385800211169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11231403890673028800563117 4211776459002385800211169)
                  ·
                    refine ⟨3158832344251789350158377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4211776459002385800211169 3158832344251789350158377)
                    ·
                      refine ⟨2369124258188842012618783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158832344251789350158377 2369124258188842012618783)
                      ·
                        rfl

theorem cell23_4613853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4613853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613853 prefixEnd_4613853 := by exact prefixLift 4613853
  have htrace : WordTrace (prefixWord ++ tailWord_4613853) baseStart_4613853 baseEnd_4613853 := by
    simpa [prefixWord, tailWord_4613853, baseEnd_4613853] using wordTrace_append hprefix tailTrace_4613853
  have hstable : (prefixWord ++ tailWord_4613853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613853).length < 2 ^ (prefixWord ++ tailWord_4613853).sum := by decide
  have hdescent : baseEnd_4613853 < baseStart_4613853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613863 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 2, 4]
def baseStart_4613863 : Nat := 118140960795 + 4613863 * 2 ^ 59
def prefixEnd_4613863 : Nat := 4983230072969 + 3 ^ 40 * 4613863 * 2
def baseEnd_4613863 : Nat := 789709797665128991164579

theorem tailTrace_4613863 : CollatzResearch.WordTrace tailWord_4613863 prefixEnd_4613863 789709797665128991164579 := by
  unfold tailWord_4613863
  simp only [CollatzResearch.WordTrace]
  refine ⟨168281408483769810910814243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112187605655846540607209495 168281408483769810910814243)
  ·
    refine ⟨252422112725654716366221365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168281408483769810910814243 252422112725654716366221365)
    ·
      refine ⟨23664573068030129659333253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 252422112725654716366221365 23664573068030129659333253)
      ·
        refine ⟨4437107450255649311124985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23664573068030129659333253 4437107450255649311124985)
        ·
          refine ⟨3327830587691736983343739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4437107450255649311124985 3327830587691736983343739)
          ·
            refine ⟨4991745881537605475015609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327830587691736983343739 4991745881537605475015609)
            ·
              refine ⟨3743809411153204106261707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4991745881537605475015609 3743809411153204106261707)
              ·
                refine ⟨5615714116729806159392561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3743809411153204106261707 5615714116729806159392561)
                ·
                  refine ⟨4211785587547354619544421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5615714116729806159392561 4211785587547354619544421)
                  ·
                    refine ⟨789709797665128991164579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211785587547354619544421 789709797665128991164579)
                    ·
                      rfl

theorem cell23_4613863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_4613863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613863 prefixEnd_4613863 := by exact prefixLift 4613863
  have htrace : WordTrace (prefixWord ++ tailWord_4613863) baseStart_4613863 baseEnd_4613863 := by
    simpa [prefixWord, tailWord_4613863, baseEnd_4613863] using wordTrace_append hprefix tailTrace_4613863
  have hstable : (prefixWord ++ tailWord_4613863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613863).length < 2 ^ (prefixWord ++ tailWord_4613863).sum := by decide
  have hdescent : baseEnd_4613863 < baseStart_4613863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613868 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_4613868 : Nat := 118140960795 + 4613868 * 2 ^ 59
def prefixEnd_4613868 : Nat := 4983230072969 + 3 ^ 40 * 4613868 * 2
def baseEnd_4613868 : Nat := 789710653466219817977071

theorem tailTrace_4613868 : CollatzResearch.WordTrace tailWord_4613868 prefixEnd_4613868 789710653466219817977071 := by
  unfold tailWord_4613868
  simp only [CollatzResearch.WordTrace]
  refine ⟨84140795424375848382373129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112187727232501131176497505 84140795424375848382373129)
  ·
    refine ⟨63105596568281886286779847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84140795424375848382373129 63105596568281886286779847)
    ·
      refine ⟨94658394852422829430169771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63105596568281886286779847 94658394852422829430169771)
      ·
        refine ⟨141987592278634244145254657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94658394852422829430169771 141987592278634244145254657)
        ·
          refine ⟨106490694208975683108940993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141987592278634244145254657 106490694208975683108940993)
          ·
            refine ⟨79868020656731762331705745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106490694208975683108940993 79868020656731762331705745)
            ·
              refine ⟨59901015492548821748779309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79868020656731762331705745 59901015492548821748779309)
              ·
                refine ⟨22462880809705808155792241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59901015492548821748779309 22462880809705808155792241)
                ·
                  refine ⟨16847160607279356116844181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22462880809705808155792241 16847160607279356116844181)
                  ·
                    refine ⟨789710653466219817977071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16847160607279356116844181 789710653466219817977071)
                    ·
                      rfl

theorem cell23_4613868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_4613868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613868 prefixEnd_4613868 := by exact prefixLift 4613868
  have htrace : WordTrace (prefixWord ++ tailWord_4613868) baseStart_4613868 baseEnd_4613868 := by
    simpa [prefixWord, tailWord_4613868, baseEnd_4613868] using wordTrace_append hprefix tailTrace_4613868
  have hstable : (prefixWord ++ tailWord_4613868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613868).length < 2 ^ (prefixWord ++ tailWord_4613868).sum := by decide
  have hdescent : baseEnd_4613868 < baseStart_4613868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613869 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_4613869 : Nat := 118140960795 + 4613869 * 2 ^ 59
def prefixEnd_4613869 : Nat := 4983230072969 + 3 ^ 40 * 4613869 * 2
def baseEnd_4613869 : Nat := 2369132473879313950018709

theorem tailTrace_4613869 : CollatzResearch.WordTrace tailWord_4613869 prefixEnd_4613869 2369132473879313950018709 := by
  unfold tailWord_4613869
  simp only [CollatzResearch.WordTrace]
  refine ⟨168281627321748073935532661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112187751547832049290355107 168281627321748073935532661)
  ·
    refine ⟨15776402561413881931456187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168281627321748073935532661 15776402561413881931456187)
    ·
      refine ⟨23664603842120822897184281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15776402561413881931456187 23664603842120822897184281)
      ·
        refine ⟨17748452881590617172888211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23664603842120822897184281 17748452881590617172888211)
        ·
          refine ⟨26622679322385925759332317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17748452881590617172888211 26622679322385925759332317)
          ·
            refine ⟨9983504745894722159749619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26622679322385925759332317 9983504745894722159749619)
            ·
              refine ⟨14975257118842083239624429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9983504745894722159749619 14975257118842083239624429)
              ·
                refine ⟨5615721419565781214859161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14975257118842083239624429 5615721419565781214859161)
                ·
                  refine ⟨4211791064674335911144371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5615721419565781214859161 4211791064674335911144371)
                  ·
                    refine ⟨6317686597011503866716557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4211791064674335911144371 6317686597011503866716557)
                    ·
                      refine ⟨2369132473879313950018709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6317686597011503866716557 2369132473879313950018709)
                      ·
                        rfl

theorem cell23_4613869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_4613869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613869 prefixEnd_4613869 := by exact prefixLift 4613869
  have htrace : WordTrace (prefixWord ++ tailWord_4613869) baseStart_4613869 baseEnd_4613869 := by
    simpa [prefixWord, tailWord_4613869, baseEnd_4613869] using wordTrace_append hprefix tailTrace_4613869
  have hstable : (prefixWord ++ tailWord_4613869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613869).length < 2 ^ (prefixWord ++ tailWord_4613869).sum := by decide
  have hdescent : baseEnd_4613869 < baseStart_4613869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613888 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_4613888 : Nat := 118140960795 + 4613888 * 2 ^ 59
def prefixEnd_4613888 : Nat := 4983230072969 + 3 ^ 40 * 4613888 * 2
def baseEnd_4613888 : Nat := 2369142230011749375681121

theorem tailTrace_4613888 : CollatzResearch.WordTrace tailWord_4613888 prefixEnd_4613888 2369142230011749375681121 := by
  unfold tailWord_4613888
  simp only [CollatzResearch.WordTrace]
  refine ⟨84141160154339620090237159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112188213539119493453649545 84141160154339620090237159)
  ·
    refine ⟨126211740231509430135355739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84141160154339620090237159 126211740231509430135355739)
    ·
      refine ⟨189317610347264145203033609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126211740231509430135355739 189317610347264145203033609)
      ·
        refine ⟨141988207760448108902275207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189317610347264145203033609 141988207760448108902275207)
        ·
          refine ⟨212982311640672163353412811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141988207760448108902275207 212982311640672163353412811)
          ·
            refine ⟨319473467461008245030119217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212982311640672163353412811 319473467461008245030119217)
            ·
              refine ⟨239605100595756183772589413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319473467461008245030119217 239605100595756183772589413)
              ·
                refine ⟨44925956361704284457360515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239605100595756183772589413 44925956361704284457360515)
                ·
                  refine ⟨67388934542556426686040773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44925956361704284457360515 67388934542556426686040773)
                  ·
                    refine ⟨12635425226729330003632645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67388934542556426686040773 12635425226729330003632645)
                    ·
                      refine ⟨2369142230011749375681121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12635425226729330003632645 2369142230011749375681121)
                      ·
                        rfl

theorem cell23_4613888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_4613888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613888 prefixEnd_4613888 := by exact prefixLift 4613888
  have htrace : WordTrace (prefixWord ++ tailWord_4613888) baseStart_4613888 baseEnd_4613888 := by
    simpa [prefixWord, tailWord_4613888, baseEnd_4613888] using wordTrace_append hprefix tailTrace_4613888
  have hstable : (prefixWord ++ tailWord_4613888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613888).length < 2 ^ (prefixWord ++ tailWord_4613888).sum := by decide
  have hdescent : baseEnd_4613888 < baseStart_4613888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613892 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_4613892 : Nat := 118140960795 + 4613892 * 2 ^ 59
def prefixEnd_4613892 : Nat := 4983230072969 + 3 ^ 40 * 4613892 * 2
def baseEnd_4613892 : Nat := 2369144283934367360031103

theorem tailTrace_4613892 : CollatzResearch.WordTrace tailWord_4613892 prefixEnd_4613892 2369144283934367360031103 := by
  unfold tailWord_4613892
  simp only [CollatzResearch.WordTrace]
  refine ⟨84141233100332374431809965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112188310800443165909079953 84141233100332374431809965)
  ·
    refine ⟨31552962412624640411928737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84141233100332374431809965 31552962412624640411928737)
    ·
      refine ⟨23664721809468480308946553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31552962412624640411928737 23664721809468480308946553)
      ·
        refine ⟨17748541357101360231709915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23664721809468480308946553 17748541357101360231709915)
        ·
          refine ⟨26622812035652040347564873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17748541357101360231709915 26622812035652040347564873)
          ·
            refine ⟨19967109026739030260673655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26622812035652040347564873 19967109026739030260673655)
            ·
              refine ⟨29950663540108545391010483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19967109026739030260673655 29950663540108545391010483)
              ·
                refine ⟨44925995310162818086515725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29950663540108545391010483 44925995310162818086515725)
                ·
                  refine ⟨16847248241311056782443397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44925995310162818086515725 16847248241311056782443397)
                  ·
                    refine ⟨3158859045245823146708137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16847248241311056782443397 3158859045245823146708137)
                    ·
                      refine ⟨2369144283934367360031103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158859045245823146708137 2369144283934367360031103)
                      ·
                        rfl

theorem cell23_4613892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_4613892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613892 prefixEnd_4613892 := by exact prefixLift 4613892
  have htrace : WordTrace (prefixWord ++ tailWord_4613892) baseStart_4613892 baseEnd_4613892 := by
    simpa [prefixWord, tailWord_4613892, baseEnd_4613892] using wordTrace_append hprefix tailTrace_4613892
  have hstable : (prefixWord ++ tailWord_4613892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613892).length < 2 ^ (prefixWord ++ tailWord_4613892).sum := by decide
  have hdescent : baseEnd_4613892 < baseStart_4613892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613909 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 2, 2, 2]
def baseStart_4613909 : Nat := 118140960795 + 4613909 * 2 ^ 59
def prefixEnd_4613909 : Nat := 4983230072969 + 3 ^ 40 * 4613909 * 2
def baseEnd_4613909 : Nat := 2369153013105493793518525

theorem tailTrace_4613909 : CollatzResearch.WordTrace tailWord_4613909 prefixEnd_4613909 2369153013105493793518525 := by
  unfold tailWord_4613909
  simp only [CollatzResearch.WordTrace]
  refine ⟨168283086241603160766988781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112188724161068773844659187 168283086241603160766988781)
  ·
    refine ⟨63106157340601185287620793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168283086241603160766988781 63106157340601185287620793)
    ·
      refine ⟨47329618005450888965715595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63106157340601185287620793 47329618005450888965715595)
      ·
        refine ⟨70994427008176333448573393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47329618005450888965715595 70994427008176333448573393)
        ·
          refine ⟨53245820256132250086430045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70994427008176333448573393 53245820256132250086430045)
          ·
            refine ⟨19967182596049593782411267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53245820256132250086430045 19967182596049593782411267)
            ·
              refine ⟨29950773894074390673616901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19967182596049593782411267 29950773894074390673616901)
              ·
                refine ⟨5615770105138948251303169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29950773894074390673616901 5615770105138948251303169)
                ·
                  refine ⟨4211827578854211188477377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5615770105138948251303169 4211827578854211188477377)
                  ·
                    refine ⟨3158870684140658391358033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4211827578854211188477377 3158870684140658391358033)
                    ·
                      refine ⟨2369153013105493793518525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158870684140658391358033 2369153013105493793518525)
                      ·
                        rfl

theorem cell23_4613909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_4613909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613909 prefixEnd_4613909 := by exact prefixLift 4613909
  have htrace : WordTrace (prefixWord ++ tailWord_4613909) baseStart_4613909 baseEnd_4613909 := by
    simpa [prefixWord, tailWord_4613909, baseEnd_4613909] using wordTrace_append hprefix tailTrace_4613909
  have hstable : (prefixWord ++ tailWord_4613909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613909).length < 2 ^ (prefixWord ++ tailWord_4613909).sum := by decide
  have hdescent : baseEnd_4613909 < baseStart_4613909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613915 : List Nat := [1, 1, 1, 1, 1, 1, 4, 8, 5]
def baseStart_4613915 : Nat := 118140960795 + 4613915 * 2 ^ 59
def prefixEnd_4613915 : Nat := 4983230072969 + 3 ^ 40 * 4613915 * 2
def baseEnd_4613915 : Nat := 263239565998824530004833

theorem tailTrace_4613915 : CollatzResearch.WordTrace tailWord_4613915 prefixEnd_4613915 263239565998824530004833 := by
  unfold tailWord_4613915
  simp only [CollatzResearch.WordTrace]
  refine ⟨168283305079581423791707199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112188870053054282527804799 168283305079581423791707199)
  ·
    refine ⟨252424957619372135687560799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168283305079581423791707199 252424957619372135687560799)
    ·
      refine ⟨378637436429058203531341199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252424957619372135687560799 378637436429058203531341199)
      ·
        refine ⟨567956154643587305297011799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378637436429058203531341199 567956154643587305297011799)
        ·
          refine ⟨851934231965380957945517699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567956154643587305297011799 851934231965380957945517699)
          ·
            refine ⟨1277901347948071436918276549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851934231965380957945517699 1277901347948071436918276549)
            ·
              refine ⟨239606502740263394422176853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1277901347948071436918276549 239606502740263394422176853)
              ·
                refine ⟨2807888703987461653384885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 239606502740263394422176853 2807888703987461653384885)
                ·
                  refine ⟨263239565998824530004833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2807888703987461653384885 263239565998824530004833)
                  ·
                    rfl

theorem cell23_4613915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 5].length) (baseStart_4613915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613915 prefixEnd_4613915 := by exact prefixLift 4613915
  have htrace : WordTrace (prefixWord ++ tailWord_4613915) baseStart_4613915 baseEnd_4613915 := by
    simpa [prefixWord, tailWord_4613915, baseEnd_4613915] using wordTrace_append hprefix tailTrace_4613915
  have hstable : (prefixWord ++ tailWord_4613915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613915).length < 2 ^ (prefixWord ++ tailWord_4613915).sum := by decide
  have hdescent : baseEnd_4613915 < baseStart_4613915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613925 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 1, 5, 3]
def baseStart_4613925 : Nat := 118140960795 + 4613925 * 2 ^ 59
def prefixEnd_4613925 : Nat := 4983230072969 + 3 ^ 40 * 4613925 * 2
def baseEnd_4613925 : Nat := 2369161228795965730918451

theorem tailTrace_4613925 : CollatzResearch.WordTrace tailWord_4613925 prefixEnd_4613925 2369161228795965730918451 := by
  unfold tailWord_4613925
  simp only [CollatzResearch.WordTrace]
  refine ⟨168283669809545195499571229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112189113206363463666380819 168283669809545195499571229)
  ·
    refine ⟨63106376178579448312339211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168283669809545195499571229 63106376178579448312339211)
    ·
      refine ⟨94659564267869172468508817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63106376178579448312339211 94659564267869172468508817)
      ·
        refine ⟨70994673200901879351381613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94659564267869172468508817 70994673200901879351381613)
        ·
          refine ⟨26623002450338204756768105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70994673200901879351381613 26623002450338204756768105)
          ·
            refine ⟨19967251837753653567576079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26623002450338204756768105 19967251837753653567576079)
            ·
              refine ⟨29950877756630480351364119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19967251837753653567576079 29950877756630480351364119)
              ·
                refine ⟨44926316634945720527046179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29950877756630480351364119 44926316634945720527046179)
                ·
                  refine ⟨67389474952418580790569269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44926316634945720527046179 67389474952418580790569269)
                  ·
                    refine ⟨6317763276789241949115869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67389474952418580790569269 6317763276789241949115869)
                    ·
                      refine ⟨2369161228795965730918451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6317763276789241949115869 2369161228795965730918451)
                      ·
                        rfl

theorem cell23_4613925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_4613925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613925 prefixEnd_4613925 := by exact prefixLift 4613925
  have htrace : WordTrace (prefixWord ++ tailWord_4613925) baseStart_4613925 baseEnd_4613925 := by
    simpa [prefixWord, tailWord_4613925, baseEnd_4613925] using wordTrace_append hprefix tailTrace_4613925
  have hstable : (prefixWord ++ tailWord_4613925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613925).length < 2 ^ (prefixWord ++ tailWord_4613925).sum := by decide
  have hdescent : baseEnd_4613925 < baseStart_4613925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613949 : List Nat := [1, 4, 1, 4, 1, 2, 2, 3, 5]
def baseStart_4613949 : Nat := 118140960795 + 4613949 * 2 ^ 59
def prefixEnd_4613949 : Nat := 4983230072969 + 3 ^ 40 * 4613949 * 2
def baseEnd_4613949 : Nat := 263241505814630404113149

theorem tailTrace_4613949 : CollatzResearch.WordTrace tailWord_4613949 prefixEnd_4613949 263241505814630404113149 := by
  unfold tailWord_4613949
  simp only [CollatzResearch.WordTrace]
  refine ⟨168284545161458247598444901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112189696774305498398963267 168284545161458247598444901)
  ·
    refine ⟨31553352217773421424708419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168284545161458247598444901 31553352217773421424708419)
    ·
      refine ⟨47330028326660132137062629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31553352217773421424708419 47330028326660132137062629)
      ·
        refine ⟨8874380311248774775699243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47330028326660132137062629 8874380311248774775699243)
        ·
          refine ⟨13311570466873162163548865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8874380311248774775699243 13311570466873162163548865)
          ·
            refine ⟨9983677850154871622661649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13311570466873162163548865 9983677850154871622661649)
            ·
              refine ⟨7487758387616153716996237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9983677850154871622661649 7487758387616153716996237)
              ·
                refine ⟨2807909395356057643873589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7487758387616153716996237 2807909395356057643873589)
                ·
                  refine ⟨263241505814630404113149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2807909395356057643873589 263241505814630404113149)
                  ·
                    rfl

theorem cell23_4613949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_4613949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613949 prefixEnd_4613949 := by exact prefixLift 4613949
  have htrace : WordTrace (prefixWord ++ tailWord_4613949) baseStart_4613949 baseEnd_4613949 := by
    simpa [prefixWord, tailWord_4613949, baseEnd_4613949] using wordTrace_append hprefix tailTrace_4613949
  have hstable : (prefixWord ++ tailWord_4613949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613949).length < 2 ^ (prefixWord ++ tailWord_4613949).sum := by decide
  have hdescent : baseEnd_4613949 < baseStart_4613949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613985 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_4613985 : Nat := 118140960795 + 4613985 * 2 ^ 59
def prefixEnd_4613985 : Nat := 4983230072969 + 3 ^ 40 * 4613985 * 2
def baseEnd_4613985 : Nat := 2369192037635235496168175

theorem tailTrace_4613985 : CollatzResearch.WordTrace tailWord_4613985 prefixEnd_4613985 2369192037635235496168175 := by
  unfold tailWord_4613985
  simp only [CollatzResearch.WordTrace]
  refine ⟨168285858189327825746755409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112190572126218550497836939 168285858189327825746755409)
  ·
    refine ⟨126214393641995869310066557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168285858189327825746755409 126214393641995869310066557)
    ·
      refine ⟨47330397615748450991274959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126214393641995869310066557 47330397615748450991274959)
      ·
        refine ⟨70995596423622676486912439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47330397615748450991274959 70995596423622676486912439)
        ·
          refine ⟨106493394635434014730368659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70995596423622676486912439 106493394635434014730368659)
          ·
            refine ⟨159740091953151022095552989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106493394635434014730368659 159740091953151022095552989)
            ·
              refine ⟨59902534482431633285832371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159740091953151022095552989 59902534482431633285832371)
              ·
                refine ⟨89853801723647449928748557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59902534482431633285832371 89853801723647449928748557)
                ·
                  refine ⟨33695175646367793723280709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89853801723647449928748557 33695175646367793723280709)
                  ·
                    refine ⟨6317845433693961323115133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33695175646367793723280709 6317845433693961323115133)
                    ·
                      refine ⟨2369192037635235496168175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6317845433693961323115133 2369192037635235496168175)
                      ·
                        rfl

theorem cell23_4613985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_4613985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613985 prefixEnd_4613985 := by exact prefixLift 4613985
  have htrace : WordTrace (prefixWord ++ tailWord_4613985) baseStart_4613985 baseEnd_4613985 := by
    simpa [prefixWord, tailWord_4613985, baseEnd_4613985] using wordTrace_append hprefix tailTrace_4613985
  have hstable : (prefixWord ++ tailWord_4613985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613985).length < 2 ^ (prefixWord ++ tailWord_4613985).sum := by decide
  have hdescent : baseEnd_4613985 < baseStart_4613985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613992 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 3, 4]
def baseStart_4613992 : Nat := 118140960795 + 4613992 * 2 ^ 59
def prefixEnd_4613992 : Nat := 4983230072969 + 3 ^ 40 * 4613992 * 2
def baseEnd_4613992 : Nat := 789731877333272322926881

theorem tailTrace_4613992 : CollatzResearch.WordTrace tailWord_4613992 prefixEnd_4613992 789731877333272322926881 := by
  unfold tailWord_4613992
  simp only [CollatzResearch.WordTrace]
  refine ⟨84143056750151232971130115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112190742333534977294840153 84143056750151232971130115)
  ·
    refine ⟨126214585125226849456695173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84143056750151232971130115 126214585125226849456695173)
    ·
      refine ⟨23665234710980034273130345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126214585125226849456695173 23665234710980034273130345)
      ·
        refine ⟨17748926033235025704847759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23665234710980034273130345 17748926033235025704847759)
        ·
          refine ⟨26623389049852538557271639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17748926033235025704847759 26623389049852538557271639)
          ·
            refine ⟨39935083574778807835907459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26623389049852538557271639 39935083574778807835907459)
            ·
              refine ⟨59902625362168211753861189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39935083574778807835907459 59902625362168211753861189)
              ·
                refine ⟨11231742255406539703848973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59902625362168211753861189 11231742255406539703848973)
                ·
                  refine ⟨4211903345777452388943365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11231742255406539703848973 4211903345777452388943365)
                  ·
                    refine ⟨789731877333272322926881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211903345777452388943365 789731877333272322926881)
                    ·
                      rfl

theorem cell23_4613992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_4613992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613992 prefixEnd_4613992 := by exact prefixLift 4613992
  have htrace : WordTrace (prefixWord ++ tailWord_4613992) baseStart_4613992 baseEnd_4613992 := by
    simpa [prefixWord, tailWord_4613992, baseEnd_4613992] using wordTrace_append hprefix tailTrace_4613992
  have hstable : (prefixWord ++ tailWord_4613992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613992).length < 2 ^ (prefixWord ++ tailWord_4613992).sum := by decide
  have hdescent : baseEnd_4613992 < baseStart_4613992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614002 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_4614002 : Nat := 118140960795 + 4614002 * 2 ^ 59
def prefixEnd_4614002 : Nat := 4983230072969 + 3 ^ 40 * 4614002 * 2
def baseEnd_4614002 : Nat := 2369200766806361929655597

theorem tailTrace_4614002 : CollatzResearch.WordTrace tailWord_4614002 prefixEnd_4614002 2369200766806361929655597 := by
  unfold tailWord_4614002
  simp only [CollatzResearch.WordTrace]
  refine ⟨42071619557566559412531065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112190985486844158433416173 42071619557566559412531065)
  ·
    refine ⟨31553714668174919559398299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42071619557566559412531065 31553714668174919559398299)
    ·
      refine ⟨47330572002262379339097449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31553714668174919559398299 47330572002262379339097449)
      ·
        refine ⟨35497929001696784504323087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47330572002262379339097449 35497929001696784504323087)
        ·
          refine ⟨53246893502545176756484631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35497929001696784504323087 53246893502545176756484631)
          ·
            refine ⟨79870340253817765134726947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53246893502545176756484631 79870340253817765134726947)
            ·
              refine ⟨119805510380726647702090421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79870340253817765134726947 119805510380726647702090421)
              ·
                refine ⟨11231766598193123222070977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119805510380726647702090421 11231766598193123222070977)
                ·
                  refine ⟨8423824948644842416553233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11231766598193123222070977 8423824948644842416553233)
                  ·
                    refine ⟨6317868711483631812414925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8423824948644842416553233 6317868711483631812414925)
                    ·
                      refine ⟨2369200766806361929655597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6317868711483631812414925 2369200766806361929655597)
                      ·
                        rfl

theorem cell23_4614002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_4614002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614002 prefixEnd_4614002 := by exact prefixLift 4614002
  have htrace : WordTrace (prefixWord ++ tailWord_4614002) baseStart_4614002 baseEnd_4614002 := by
    simpa [prefixWord, tailWord_4614002, baseEnd_4614002] using wordTrace_append hprefix tailTrace_4614002
  have hstable : (prefixWord ++ tailWord_4614002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614002).length < 2 ^ (prefixWord ++ tailWord_4614002).sum := by decide
  have hdescent : baseEnd_4614002 < baseStart_4614002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614005 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 10]
def baseStart_4614005 : Nat := 118140960795 + 4614005 * 2 ^ 59
def prefixEnd_4614005 : Nat := 4983230072969 + 3 ^ 40 * 4614005 * 2
def baseEnd_4614005 : Nat := 263244700805369490879787

theorem tailTrace_4614005 : CollatzResearch.WordTrace tailWord_4614005 prefixEnd_4614005 263244700805369490879787 := by
  unfold tailWord_4614005
  simp only [CollatzResearch.WordTrace]
  refine ⟨168286587649255369162483469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112191058432836912774988979 168286587649255369162483469)
  ·
    refine ⟨63107470368470763435931301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168286587649255369162483469 63107470368470763435931301)
    ·
      refine ⟨11832650694088268144237119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63107470368470763435931301 11832650694088268144237119)
      ·
        refine ⟨17748976041132402216355679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11832650694088268144237119 17748976041132402216355679)
        ·
          refine ⟨26623464061698603324533519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17748976041132402216355679 26623464061698603324533519)
          ·
            refine ⟨39935196092547904986800279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26623464061698603324533519 39935196092547904986800279)
            ·
              refine ⟨59902794138821857480200419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39935196092547904986800279 59902794138821857480200419)
              ·
                refine ⟨89854191208232786220300629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59902794138821857480200419 89854191208232786220300629)
                ·
                  refine ⟨263244700805369490879787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89854191208232786220300629 263244700805369490879787)
                  ·
                    rfl

theorem cell23_4614005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_4614005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614005 prefixEnd_4614005 := by exact prefixLift 4614005
  have htrace : WordTrace (prefixWord ++ tailWord_4614005) baseStart_4614005 baseEnd_4614005 := by
    simpa [prefixWord, tailWord_4614005, baseEnd_4614005] using wordTrace_append hprefix tailTrace_4614005
  have hstable : (prefixWord ++ tailWord_4614005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614005).length < 2 ^ (prefixWord ++ tailWord_4614005).sum := by decide
  have hdescent : baseEnd_4614005 < baseStart_4614005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614026 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_4614026 : Nat := 118140960795 + 4614026 * 2 ^ 59
def prefixEnd_4614026 : Nat := 4983230072969 + 3 ^ 40 * 4614026 * 2
def baseEnd_4614026 : Nat := 789737696780689945251829

theorem tailTrace_4614026 : CollatzResearch.WordTrace tailWord_4614026 prefixEnd_4614026 789737696780689945251829 := by
  unfold tailWord_4614026
  simp only [CollatzResearch.WordTrace]
  refine ⟨42071838395544822437249483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112191569054786193165998621 42071838395544822437249483)
  ·
    refine ⟨63107757593317233655874225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42071838395544822437249483 63107757593317233655874225)
    ·
      refine ⟨47330818194987925241905669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63107757593317233655874225 47330818194987925241905669)
      ·
        refine ⟨8874528411560235982857313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47330818194987925241905669 8874528411560235982857313)
        ·
          refine ⟨6655896308670176987142985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8874528411560235982857313 6655896308670176987142985)
          ·
            refine ⟨4991922231502632740357239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6655896308670176987142985 4991922231502632740357239)
            ·
              refine ⟨7487883347253949110535859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4991922231502632740357239 7487883347253949110535859)
              ·
                refine ⟨11231825020880923665803789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7487883347253949110535859 11231825020880923665803789)
                ·
                  refine ⟨4211934382830346374676421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11231825020880923665803789 4211934382830346374676421)
                  ·
                    refine ⟨789737696780689945251829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211934382830346374676421 789737696780689945251829)
                    ·
                      rfl

theorem cell23_4614026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_4614026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614026 prefixEnd_4614026 := by exact prefixLift 4614026
  have htrace : WordTrace (prefixWord ++ tailWord_4614026) baseStart_4614026 baseEnd_4614026 := by
    simpa [prefixWord, tailWord_4614026, baseEnd_4614026] using wordTrace_append hprefix tailTrace_4614026
  have hstable : (prefixWord ++ tailWord_4614026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614026).length < 2 ^ (prefixWord ++ tailWord_4614026).sum := by decide
  have hdescent : baseEnd_4614026 < baseStart_4614026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614039 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 6]
def baseStart_4614039 : Nat := 118140960795 + 4614039 * 2 ^ 59
def prefixEnd_4614039 : Nat := 4983230072969 + 3 ^ 40 * 4614039 * 2
def baseEnd_4614039 : Nat := 263246640621175364988103

theorem tailTrace_4614039 : CollatzResearch.WordTrace tailWord_4614039 prefixEnd_4614039 263246640621175364988103 := by
  unfold tailWord_4614039
  simp only [CollatzResearch.WordTrace]
  refine ⟨168287827731132192969221171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112191885154088128646147447 168287827731132192969221171)
  ·
    refine ⟨252431741596698289453831757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168287827731132192969221171 252431741596698289453831757)
    ·
      refine ⟨94661903098761858545186909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252431741596698289453831757 94661903098761858545186909)
      ·
        refine ⟨35498213662035696954445091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94661903098761858545186909 35498213662035696954445091)
        ·
          refine ⟨53247320493053545431667637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35498213662035696954445091 53247320493053545431667637)
          ·
            refine ⟨4991936296223769884218841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53247320493053545431667637 4991936296223769884218841)
            ·
              refine ⟨3743952222167827413164131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4991936296223769884218841 3743952222167827413164131)
              ·
                refine ⟨5615928333251741119746197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3743952222167827413164131 5615928333251741119746197)
                ·
                  refine ⟨263246640621175364988103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5615928333251741119746197 263246640621175364988103)
                  ·
                    rfl

theorem cell23_4614039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 6].length) (baseStart_4614039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614039 prefixEnd_4614039 := by exact prefixLift 4614039
  have htrace : WordTrace (prefixWord ++ tailWord_4614039) baseStart_4614039 baseEnd_4614039 := by
    simpa [prefixWord, tailWord_4614039, baseEnd_4614039] using wordTrace_append hprefix tailTrace_4614039
  have hstable : (prefixWord ++ tailWord_4614039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614039).length < 2 ^ (prefixWord ++ tailWord_4614039).sum := by decide
  have hdescent : baseEnd_4614039 < baseStart_4614039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614052 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_4614052 : Nat := 118140960795 + 4614052 * 2 ^ 59
def prefixEnd_4614052 : Nat := 4983230072969 + 3 ^ 40 * 4614052 * 2
def baseEnd_4614052 : Nat := 789742146946362244676789

theorem tailTrace_4614052 : CollatzResearch.WordTrace tailWord_4614052 prefixEnd_4614052 789742146946362244676789 := by
  unfold tailWord_4614052
  simp only [CollatzResearch.WordTrace]
  refine ⟨84144150940042548094722205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112192201253390064126296273 84144150940042548094722205)
  ·
    refine ⟨31554056602515955535520827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84144150940042548094722205 31554056602515955535520827)
    ·
      refine ⟨47331084903773933303281241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31554056602515955535520827 47331084903773933303281241)
      ·
        refine ⟨35498313677830449977460931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47331084903773933303281241 35498313677830449977460931)
        ·
          refine ⟨53247470516745674966191397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35498313677830449977460931 53247470516745674966191397)
          ·
            refine ⟨9983900721889814056160887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53247470516745674966191397 9983900721889814056160887)
            ·
              refine ⟨14975851082834721084241331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9983900721889814056160887 14975851082834721084241331)
              ·
                refine ⟨22463776624252081626361997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14975851082834721084241331 22463776624252081626361997)
                ·
                  refine ⟨8423916234094530609885749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22463776624252081626361997 8423916234094530609885749)
                  ·
                    refine ⟨789742146946362244676789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8423916234094530609885749 789742146946362244676789)
                    ·
                      rfl

theorem cell23_4614052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_4614052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614052 prefixEnd_4614052 := by exact prefixLift 4614052
  have htrace : WordTrace (prefixWord ++ tailWord_4614052) baseStart_4614052 baseEnd_4614052 := by
    simpa [prefixWord, tailWord_4614052, baseEnd_4614052] using wordTrace_append hprefix tailTrace_4614052
  have hstable : (prefixWord ++ tailWord_4614052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614052).length < 2 ^ (prefixWord ++ tailWord_4614052).sum := by decide
  have hdescent : baseEnd_4614052 < baseStart_4614052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614085 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_4614085 : Nat := 118140960795 + 4614085 * 2 ^ 59
def prefixEnd_4614085 : Nat := 4983230072969 + 3 ^ 40 * 4614085 * 2
def baseEnd_4614085 : Nat := 2369243385700685104917715

theorem tailTrace_4614085 : CollatzResearch.WordTrace tailWord_4614085 prefixEnd_4614085 2369243385700685104917715 := by
  unfold tailWord_4614085
  simp only [CollatzResearch.WordTrace]
  refine ⟨168289505488965542825395709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112193003659310361883597139 168289505488965542825395709)
  ·
    refine ⟨63108564558362078559523391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168289505488965542825395709 63108564558362078559523391)
    ·
      refine ⟨94662846837543117839285087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63108564558362078559523391 94662846837543117839285087)
      ·
        refine ⟨141994270256314676758927631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94662846837543117839285087 141994270256314676758927631)
        ·
          refine ⟨212991405384472015138391447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141994270256314676758927631 212991405384472015138391447)
          ·
            refine ⟨319487108076708022707587171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212991405384472015138391447 319487108076708022707587171)
            ·
              refine ⟨479230662115062034061380757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319487108076708022707587171 479230662115062034061380757)
              ·
                refine ⟨22463937286643532846627223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 479230662115062034061380757 22463937286643532846627223)
                ·
                  refine ⟨33695905929965299269940835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22463937286643532846627223 33695905929965299269940835)
                  ·
                    refine ⟨50543858894947948904911253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33695905929965299269940835 50543858894947948904911253)
                    ·
                      refine ⟨2369243385700685104917715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50543858894947948904911253 2369243385700685104917715)
                      ·
                        rfl

theorem cell23_4614085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_4614085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614085 prefixEnd_4614085 := by exact prefixLift 4614085
  have htrace : WordTrace (prefixWord ++ tailWord_4614085) baseStart_4614085 baseEnd_4614085 := by
    simpa [prefixWord, tailWord_4614085, baseEnd_4614085] using wordTrace_append hprefix tailTrace_4614085
  have hstable : (prefixWord ++ tailWord_4614085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614085).length < 2 ^ (prefixWord ++ tailWord_4614085).sum := by decide
  have hdescent : baseEnd_4614085 < baseStart_4614085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614126 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_4614126 : Nat := 118140960795 + 4614126 * 2 ^ 59
def prefixEnd_4614126 : Nat := 4983230072969 + 3 ^ 40 * 4614126 * 2
def baseEnd_4614126 : Nat := 2369264438407519444505027

theorem tailTrace_4614126 : CollatzResearch.WordTrace tailWord_4614126 prefixEnd_4614126 2369264438407519444505027 := by
  unfold tailWord_4614126
  simp only [CollatzResearch.WordTrace]
  refine ⟨21036375110227125853454779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112194000587878004551758821 21036375110227125853454779)
  ·
    refine ⟨31554562665340688780182169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21036375110227125853454779 31554562665340688780182169)
    ·
      refine ⟨23665921999005516585136627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31554562665340688780182169 23665921999005516585136627)
      ·
        refine ⟨35498882998508274877704941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23665921999005516585136627 35498882998508274877704941)
        ·
          refine ⟨13312081124440603079139353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35498882998508274877704941 13312081124440603079139353)
          ·
            refine ⟨9984060843330452309354515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13312081124440603079139353 9984060843330452309354515)
            ·
              refine ⟨14976091264995678464031773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9984060843330452309354515 14976091264995678464031773)
              ·
                refine ⟨5616034224373379424011915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14976091264995678464031773 5616034224373379424011915)
                ·
                  refine ⟨8424051336560069136017873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5616034224373379424011915 8424051336560069136017873)
                  ·
                    refine ⟨6318038502420051852013405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8424051336560069136017873 6318038502420051852013405)
                    ·
                      refine ⟨2369264438407519444505027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6318038502420051852013405 2369264438407519444505027)
                      ·
                        rfl

theorem cell23_4614126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_4614126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614126 prefixEnd_4614126 := by exact prefixLift 4614126
  have htrace : WordTrace (prefixWord ++ tailWord_4614126) baseStart_4614126 baseEnd_4614126 := by
    simpa [prefixWord, tailWord_4614126, baseEnd_4614126] using wordTrace_append hprefix tailTrace_4614126
  have hstable : (prefixWord ++ tailWord_4614126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614126).length < 2 ^ (prefixWord ++ tailWord_4614126).sum := by decide
  have hdescent : baseEnd_4614126 < baseStart_4614126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614179 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 3, 4, 2]
def baseStart_4614179 : Nat := 118140960795 + 4614179 * 2 ^ 59
def prefixEnd_4614179 : Nat := 4983230072969 + 3 ^ 40 * 4614179 * 2
def baseEnd_4614179 : Nat := 2369291652882207737142283

theorem tailTrace_4614179 : CollatzResearch.WordTrace tailWord_4614179 prefixEnd_4614179 2369291652882207737142283 := by
  unfold tailWord_4614179
  simp only [CollatzResearch.WordTrace]
  refine ⟨168292933950624996879317591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112195289300416664586211727 168292933950624996879317591)
  ·
    refine ⟨252439400925937495318976387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168292933950624996879317591 252439400925937495318976387)
    ·
      refine ⟨378659101388906242978464581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252439400925937495318976387 378659101388906242978464581)
      ·
        refine ⟨70998581510419920558462109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 378659101388906242978464581 70998581510419920558462109)
        ·
          refine ⟨26624468066407470209423291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70998581510419920558462109 26624468066407470209423291)
          ·
            refine ⟨39936702099611205314134937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26624468066407470209423291 39936702099611205314134937)
            ·
              refine ⟨29952526574708403985601203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39936702099611205314134937 29952526574708403985601203)
              ·
                refine ⟨44928789862062605978401805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29952526574708403985601203 44928789862062605978401805)
                ·
                  refine ⟨16848296198273477241900677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44928789862062605978401805 16848296198273477241900677)
                  ·
                    refine ⟨3159055537176276982856377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16848296198273477241900677 3159055537176276982856377)
                    ·
                      refine ⟨2369291652882207737142283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159055537176276982856377 2369291652882207737142283)
                      ·
                        rfl

theorem cell23_4614179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_4614179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614179 prefixEnd_4614179 := by exact prefixLift 4614179
  have htrace : WordTrace (prefixWord ++ tailWord_4614179) baseStart_4614179 baseEnd_4614179 := by
    simpa [prefixWord, tailWord_4614179, baseEnd_4614179] using wordTrace_append hprefix tailTrace_4614179
  have hstable : (prefixWord ++ tailWord_4614179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614179).length < 2 ^ (prefixWord ++ tailWord_4614179).sum := by decide
  have hdescent : baseEnd_4614179 < baseStart_4614179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614230 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_4614230 : Nat := 118140960795 + 4614230 * 2 ^ 59
def prefixEnd_4614230 : Nat := 4983230072969 + 3 ^ 40 * 4614230 * 2
def baseEnd_4614230 : Nat := 2369317840395587037604549

theorem tailTrace_4614230 : CollatzResearch.WordTrace tailWord_4614230 prefixEnd_4614230 2369317840395587037604549 := by
  unfold tailWord_4614230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10518424629590014536839009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112196529382293488392949429 10518424629590014536839009)
  ·
    refine ⟨7888818472192510902629257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10518424629590014536839009 7888818472192510902629257)
    ·
      refine ⟨5916613854144383176971943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7888818472192510902629257 5916613854144383176971943)
      ·
        refine ⟨8874920781216574765457915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5916613854144383176971943 8874920781216574765457915)
        ·
          refine ⟨13312381171824862148186873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8874920781216574765457915 13312381171824862148186873)
          ·
            refine ⟨9984285878868646611140155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13312381171824862148186873 9984285878868646611140155)
            ·
              refine ⟨14976428818302969916710233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9984285878868646611140155 14976428818302969916710233)
              ·
                refine ⟨11232321613727227437532675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14976428818302969916710233 11232321613727227437532675)
                ·
                  refine ⟨16848482420590841156299013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11232321613727227437532675 16848482420590841156299013)
                  ·
                    refine ⟨3159090453860782716806065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16848482420590841156299013 3159090453860782716806065)
                    ·
                      refine ⟨2369317840395587037604549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159090453860782716806065 2369317840395587037604549)
                      ·
                        rfl

theorem cell23_4614230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_4614230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614230 prefixEnd_4614230 := by exact prefixLift 4614230
  have htrace : WordTrace (prefixWord ++ tailWord_4614230) baseStart_4614230 baseEnd_4614230 := by
    simpa [prefixWord, tailWord_4614230, baseEnd_4614230] using wordTrace_append hprefix tailTrace_4614230
  have hstable : (prefixWord ++ tailWord_4614230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614230).length < 2 ^ (prefixWord ++ tailWord_4614230).sum := by decide
  have hdescent : baseEnd_4614230 < baseStart_4614230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614279 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 5, 4]
def baseStart_4614279 : Nat := 118140960795 + 4614279 * 2 ^ 59
def prefixEnd_4614279 : Nat := 4983230072969 + 3 ^ 40 * 4614279 * 2
def baseEnd_4614279 : Nat := 789781000315885781963941

theorem tailTrace_4614279 : CollatzResearch.WordTrace tailWord_4614279 prefixEnd_4614279 789781000315885781963941 := by
  unfold tailWord_4614279
  simp only [CollatzResearch.WordTrace]
  refine ⟨168296581250262713957957891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112197720833508475971971927 168296581250262713957957891)
  ·
    refine ⟨252444871875394070936936837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168296581250262713957957891 252444871875394070936936837)
    ·
      refine ⟨47333413476636388300675657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252444871875394070936936837 47333413476636388300675657)
      ·
        refine ⟨35500060107477291225506743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47333413476636388300675657 35500060107477291225506743)
        ·
          refine ⟨53250090161215936838260115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35500060107477291225506743 53250090161215936838260115)
          ·
            refine ⟨79875135241823905257390173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53250090161215936838260115 79875135241823905257390173)
            ·
              refine ⟨29953175715683964471521315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79875135241823905257390173 29953175715683964471521315)
              ·
                refine ⟨44929763573525946707281973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29953175715683964471521315 44929763573525946707281973)
                ·
                  refine ⟨4212165335018057503807685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44929763573525946707281973 4212165335018057503807685)
                  ·
                    refine ⟨789781000315885781963941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4212165335018057503807685 789781000315885781963941)
                    ·
                      rfl

theorem cell23_4614279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_4614279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614279 prefixEnd_4614279 := by exact prefixLift 4614279
  have htrace : WordTrace (prefixWord ++ tailWord_4614279) baseStart_4614279 baseEnd_4614279 := by
    simpa [prefixWord, tailWord_4614279, baseEnd_4614279] using wordTrace_append hprefix tailTrace_4614279
  have hstable : (prefixWord ++ tailWord_4614279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614279).length < 2 ^ (prefixWord ++ tailWord_4614279).sum := by decide
  have hdescent : baseEnd_4614279 < baseStart_4614279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614286 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_4614286 : Nat := 118140960795 + 4614286 * 2 ^ 59
def prefixEnd_4614286 : Nat := 4983230072969 + 3 ^ 40 * 4614286 * 2
def baseEnd_4614286 : Nat := 2369346595312238818504291

theorem tailTrace_4614286 : CollatzResearch.WordTrace tailWord_4614286 prefixEnd_4614286 2369346595312238818504291 := by
  unfold tailWord_4614286
  simp only [CollatzResearch.WordTrace]
  refine ⟨21037104570154669269182839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112197891040824902768975141 21037104570154669269182839)
  ·
    refine ⟨31555656855232003903774259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21037104570154669269182839 31555656855232003903774259)
    ·
      refine ⟨47333485282848005855661389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31555656855232003903774259 47333485282848005855661389)
      ·
        refine ⟨17750056981068002195873021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47333485282848005855661389 17750056981068002195873021)
        ·
          refine ⟨6656271367900500823452383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17750056981068002195873021 6656271367900500823452383)
          ·
            refine ⟨9984407051850751235178575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6656271367900500823452383 9984407051850751235178575)
            ·
              refine ⟨14976610577776126852767863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9984407051850751235178575 14976610577776126852767863)
              ·
                refine ⟨22464915866664190279151795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14976610577776126852767863 22464915866664190279151795)
                ·
                  refine ⟨33697373799996285418727693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22464915866664190279151795 33697373799996285418727693)
                  ·
                    refine ⟨12636515174998607032022885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33697373799996285418727693 12636515174998607032022885)
                    ·
                      refine ⟨2369346595312238818504291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12636515174998607032022885 2369346595312238818504291)
                      ·
                        rfl

theorem cell23_4614286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_4614286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614286 prefixEnd_4614286 := by exact prefixLift 4614286
  have htrace : WordTrace (prefixWord ++ tailWord_4614286) baseStart_4614286 baseEnd_4614286 := by
    simpa [prefixWord, tailWord_4614286, baseEnd_4614286] using wordTrace_append hprefix tailTrace_4614286
  have hstable : (prefixWord ++ tailWord_4614286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614286).length < 2 ^ (prefixWord ++ tailWord_4614286).sum := by decide
  have hdescent : baseEnd_4614286 < baseStart_4614286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614346 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2]
def baseStart_4614346 : Nat := 118140960795 + 4614346 * 2 ^ 59
def prefixEnd_4614346 : Nat := 4983230072969 + 3 ^ 40 * 4614346 * 2
def baseEnd_4614346 : Nat := 2369377404151508583754015

theorem tailTrace_4614346 : CollatzResearch.WordTrace tailWord_4614346 prefixEnd_4614346 2369377404151508583754015 := by
  unfold tailWord_4614346
  simp only [CollatzResearch.WordTrace]
  refine ⟨42074756235254996100161723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112199349960679989600431261 42074756235254996100161723)
  ·
    refine ⟨63112134352882494150242585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42074756235254996100161723 63112134352882494150242585)
    ·
      refine ⟨47334100764661870612681939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63112134352882494150242585 47334100764661870612681939)
      ·
        refine ⟨71001151146992805919022909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47334100764661870612681939 71001151146992805919022909)
        ·
          refine ⟨26625431680122302219633591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71001151146992805919022909 26625431680122302219633591)
          ·
            refine ⟨39938147520183453329450387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26625431680122302219633591 39938147520183453329450387)
            ·
              refine ⟨59907221280275179994175581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39938147520183453329450387 59907221280275179994175581)
              ·
                refine ⟨22465207980103192497815843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59907221280275179994175581 22465207980103192497815843)
                ·
                  refine ⟨33697811970154788746723765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22465207980103192497815843 33697811970154788746723765)
                  ·
                    refine ⟨3159169872202011445005353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33697811970154788746723765 3159169872202011445005353)
                    ·
                      refine ⟨2369377404151508583754015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159169872202011445005353 2369377404151508583754015)
                      ·
                        rfl

theorem cell23_4614346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_4614346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614346 prefixEnd_4614346 := by exact prefixLift 4614346
  have htrace : WordTrace (prefixWord ++ tailWord_4614346) baseStart_4614346 baseEnd_4614346 := by
    simpa [prefixWord, tailWord_4614346, baseEnd_4614346] using wordTrace_append hprefix tailTrace_4614346
  have hstable : (prefixWord ++ tailWord_4614346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614346).length < 2 ^ (prefixWord ++ tailWord_4614346).sum := by decide
  have hdescent : baseEnd_4614346 < baseStart_4614346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614359 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_4614359 : Nat := 118140960795 + 4614359 * 2 ^ 59
def prefixEnd_4614359 : Nat := 4983230072969 + 3 ^ 40 * 4614359 * 2
def baseEnd_4614359 : Nat := 2369384079400017032891455

theorem tailTrace_4614359 : CollatzResearch.WordTrace tailWord_4614359 prefixEnd_4614359 2369384079400017032891455 := by
  unfold tailWord_4614359
  simp only [CollatzResearch.WordTrace]
  refine ⟨168299499089972887620870131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112199666059981925080580087 168299499089972887620870131)
  ·
    refine ⟨252449248634959331431305197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168299499089972887620870131 252449248634959331431305197)
    ·
      refine ⟨94668468238109749286739449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252449248634959331431305197 94668468238109749286739449)
      ·
        refine ⟨71001351178582311965054587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94668468238109749286739449 71001351178582311965054587)
        ·
          refine ⟨106502026767873467947581881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71001351178582311965054587 106502026767873467947581881)
          ·
            refine ⟨79876520075905100960686411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106502026767873467947581881 79876520075905100960686411)
            ·
              refine ⟨119814780113857651441029617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79876520075905100960686411 119814780113857651441029617)
              ·
                refine ⟨89861085085393238580772213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119814780113857651441029617 89861085085393238580772213)
                ·
                  refine ⟨8424476726755616116947395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89861085085393238580772213 8424476726755616116947395)
                  ·
                    refine ⟨12636715090133424175421093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8424476726755616116947395 12636715090133424175421093)
                    ·
                      refine ⟨2369384079400017032891455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12636715090133424175421093 2369384079400017032891455)
                      ·
                        rfl

theorem cell23_4614359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_4614359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614359 prefixEnd_4614359 := by exact prefixLift 4614359
  have htrace : WordTrace (prefixWord ++ tailWord_4614359) baseStart_4614359 baseEnd_4614359 := by
    simpa [prefixWord, tailWord_4614359, baseEnd_4614359] using wordTrace_append hprefix tailTrace_4614359
  have hstable : (prefixWord ++ tailWord_4614359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614359).length < 2 ^ (prefixWord ++ tailWord_4614359).sum := by decide
  have hdescent : baseEnd_4614359 < baseStart_4614359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614364 : List Nat := [2, 2, 5, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4614364 : Nat := 118140960795 + 4614364 * 2 ^ 59
def prefixEnd_4614364 : Nat := 4983230072969 + 3 ^ 40 * 4614364 * 2
def baseEnd_4614364 : Nat := 789795548934429837776311

theorem tailTrace_4614364 : CollatzResearch.WordTrace tailWord_4614364 prefixEnd_4614364 789795548934429837776311 := by
  unfold tailWord_4614364
  simp only [CollatzResearch.WordTrace]
  refine ⟨84149840727477386737401073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112199787636636515649868097 84149840727477386737401073)
  ·
    refine ⟨63112380545608040053050805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84149840727477386737401073 63112380545608040053050805)
    ·
      refine ⟨5916785676150753754973513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63112380545608040053050805 5916785676150753754973513)
      ·
        refine ⟨4437589257113065316230135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5916785676150753754973513 4437589257113065316230135)
        ·
          refine ⟨6656383885669597974345203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4437589257113065316230135 6656383885669597974345203)
          ·
            refine ⟨9984575828504396961517805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6656383885669597974345203 9984575828504396961517805)
            ·
              refine ⟨3744215935689148860569177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9984575828504396961517805 3744215935689148860569177)
              ·
                refine ⟨2808161951766861645426883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744215935689148860569177 2808161951766861645426883)
                ·
                  refine ⟨4212242927650292468140325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808161951766861645426883 4212242927650292468140325)
                  ·
                    refine ⟨789795548934429837776311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4212242927650292468140325 789795548934429837776311)
                    ·
                      rfl

theorem cell23_4614364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4614364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614364 prefixEnd_4614364 := by exact prefixLift 4614364
  have htrace : WordTrace (prefixWord ++ tailWord_4614364) baseStart_4614364 baseEnd_4614364 := by
    simpa [prefixWord, tailWord_4614364, baseEnd_4614364] using wordTrace_append hprefix tailTrace_4614364
  have hstable : (prefixWord ++ tailWord_4614364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614364).length < 2 ^ (prefixWord ++ tailWord_4614364).sum := by decide
  have hdescent : baseEnd_4614364 < baseStart_4614364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614379 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 5]
def baseStart_4614379 : Nat := 118140960795 + 4614379 * 2 ^ 59
def prefixEnd_4614379 : Nat := 4983230072969 + 3 ^ 40 * 4614379 * 2
def baseEnd_4614379 : Nat := 2369394349013106954641363

theorem tailTrace_4614379 : CollatzResearch.WordTrace tailWord_4614379 prefixEnd_4614379 2369394349013106954641363 := by
  unfold tailWord_4614379
  simp only [CollatzResearch.WordTrace]
  refine ⟨168300228549900431036598191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112200152366600287357732127 168300228549900431036598191)
  ·
    refine ⟨252450342824850646554897287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168300228549900431036598191 252450342824850646554897287)
    ·
      refine ⟨378675514237275969832345931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252450342824850646554897287 378675514237275969832345931)
      ·
        refine ⟨568013271355913954748518897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378675514237275969832345931 568013271355913954748518897)
        ·
          refine ⟨426009953516935466061389173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 568013271355913954748518897 426009953516935466061389173)
          ·
            refine ⟨39938433142212699943255235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 426009953516935466061389173 39938433142212699943255235)
            ·
              refine ⟨59907649713319049914882853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39938433142212699943255235 59907649713319049914882853)
              ·
                refine ⟨11232684321247321859040535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59907649713319049914882853 11232684321247321859040535)
                ·
                  refine ⟨16849026481870982788560803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11232684321247321859040535 16849026481870982788560803)
                  ·
                    refine ⟨25273539722806474182841205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16849026481870982788560803 25273539722806474182841205)
                    ·
                      refine ⟨2369394349013106954641363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25273539722806474182841205 2369394349013106954641363)
                      ·
                        rfl

theorem cell23_4614379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 5].length) (baseStart_4614379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614379 prefixEnd_4614379 := by exact prefixLift 4614379
  have htrace : WordTrace (prefixWord ++ tailWord_4614379) baseStart_4614379 baseEnd_4614379 := by
    simpa [prefixWord, tailWord_4614379, baseEnd_4614379] using wordTrace_append hprefix tailTrace_4614379
  have hstable : (prefixWord ++ tailWord_4614379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614379).length < 2 ^ (prefixWord ++ tailWord_4614379).sum := by decide
  have hdescent : baseEnd_4614379 < baseStart_4614379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614427 : List Nat := [1, 1, 1, 1, 1, 1, 10, 2, 1, 2, 2]
def baseStart_4614427 : Nat := 118140960795 + 4614427 * 2 ^ 59
def prefixEnd_4614427 : Nat := 4983230072969 + 3 ^ 40 * 4614427 * 2
def baseEnd_4614427 : Nat := 2369418996084522766841143

theorem tailTrace_4614427 : CollatzResearch.WordTrace tailWord_4614427 prefixEnd_4614427 2369418996084522766841143 := by
  unfold tailWord_4614427
  simp only [CollatzResearch.WordTrace]
  refine ⟨168301979253726535234345535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112201319502484356822897023 168301979253726535234345535)
  ·
    refine ⟨252452968880589802851518303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168301979253726535234345535 252452968880589802851518303)
    ·
      refine ⟨378679453320884704277277455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252452968880589802851518303 378679453320884704277277455)
      ·
        refine ⟨568019179981327056415916183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378679453320884704277277455 568019179981327056415916183)
        ·
          refine ⟨852028769971990584623874275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568019179981327056415916183 852028769971990584623874275)
          ·
            refine ⟨1278043154957985876935811413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852028769971990584623874275 1278043154957985876935811413)
            ·
              refine ⟨3744267055540974248835385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1278043154957985876935811413 3744267055540974248835385)
              ·
                refine ⟨2808200291655730686626539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744267055540974248835385 2808200291655730686626539)
                ·
                  refine ⟨4212300437483596029939809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808200291655730686626539 4212300437483596029939809)
                  ·
                    refine ⟨3159225328112697022454857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4212300437483596029939809 3159225328112697022454857)
                    ·
                      refine ⟨2369418996084522766841143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159225328112697022454857 2369418996084522766841143)
                      ·
                        rfl

theorem cell23_4614427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 2, 2].length) (baseStart_4614427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614427 prefixEnd_4614427 := by exact prefixLift 4614427
  have htrace : WordTrace (prefixWord ++ tailWord_4614427) baseStart_4614427 baseEnd_4614427 := by
    simpa [prefixWord, tailWord_4614427, baseEnd_4614427] using wordTrace_append hprefix tailTrace_4614427
  have hstable : (prefixWord ++ tailWord_4614427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614427).length < 2 ^ (prefixWord ++ tailWord_4614427).sum := by decide
  have hdescent : baseEnd_4614427 < baseStart_4614427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614430 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4614430 : Nat := 118140960795 + 4614430 * 2 ^ 59
def prefixEnd_4614430 : Nat := 4983230072969 + 3 ^ 40 * 4614430 * 2
def baseEnd_4614430 : Nat := 2369420536526486255103629

theorem tailTrace_4614430 : CollatzResearch.WordTrace tailWord_4614430 prefixEnd_4614430 2369420536526486255103629 := by
  unfold tailWord_4614430
  simp only [CollatzResearch.WordTrace]
  refine ⟨21037761084089458343338093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112201392448477111164469829 21037761084089458343338093)
  ·
    refine ⟨7889160406533546878751785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21037761084089458343338093 7889160406533546878751785)
    ·
      refine ⟨5916870304900160159063839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7889160406533546878751785 5916870304900160159063839)
      ·
        refine ⟨8875305457350240238595759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5916870304900160159063839 8875305457350240238595759)
        ·
          refine ⟨13312958186025360357893639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8875305457350240238595759 13312958186025360357893639)
          ·
            refine ⟨19969437279038040536840459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13312958186025360357893639 19969437279038040536840459)
            ·
              refine ⟨29954155918557060805260689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19969437279038040536840459 29954155918557060805260689)
              ·
                refine ⟨22465616938917795603945517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29954155918557060805260689 22465616938917795603945517)
                ·
                  refine ⟨8424606352094173351479569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22465616938917795603945517 8424606352094173351479569)
                  ·
                    refine ⟨6318454764070630013609677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8424606352094173351479569 6318454764070630013609677)
                    ·
                      refine ⟨2369420536526486255103629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6318454764070630013609677 2369420536526486255103629)
                      ·
                        rfl

theorem cell23_4614430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4614430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614430 prefixEnd_4614430 := by exact prefixLift 4614430
  have htrace : WordTrace (prefixWord ++ tailWord_4614430) baseStart_4614430 baseEnd_4614430 := by
    simpa [prefixWord, tailWord_4614430, baseEnd_4614430] using wordTrace_append hprefix tailTrace_4614430
  have hstable : (prefixWord ++ tailWord_4614430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614430).length < 2 ^ (prefixWord ++ tailWord_4614430).sum := by decide
  have hdescent : baseEnd_4614430 < baseStart_4614430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614453 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_4614453 : Nat := 118140960795 + 4614453 * 2 ^ 59
def prefixEnd_4614453 : Nat := 4983230072969 + 3 ^ 40 * 4614453 * 2
def baseEnd_4614453 : Nat := 2369432346581539665116023

theorem tailTrace_4614453 : CollatzResearch.WordTrace tailWord_4614453 prefixEnd_4614453 2369432346581539665116023 := by
  unfold tailWord_4614453
  simp only [CollatzResearch.WordTrace]
  refine ⟨168302927551632341674792013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112201951701088227783194675 168302927551632341674792013)
  ·
    refine ⟨63113597831862128128047005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168302927551632341674792013 63113597831862128128047005)
    ·
      refine ⟨23667599186948298048017627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63113597831862128128047005 23667599186948298048017627)
      ·
        refine ⟨35501398780422447072026441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23667599186948298048017627 35501398780422447072026441)
        ·
          refine ⟨26626049085316835304019831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35501398780422447072026441 26626049085316835304019831)
          ·
            refine ⟨39939073627975252956029747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26626049085316835304019831 39939073627975252956029747)
            ·
              refine ⟨59908610441962879434044621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39939073627975252956029747 59908610441962879434044621)
              ·
                refine ⟨22465728915736079787766733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59908610441962879434044621 22465728915736079787766733)
                ·
                  refine ⟨8424648343401029920412525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22465728915736079787766733 8424648343401029920412525)
                  ·
                    refine ⟨3159243128775386220154697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8424648343401029920412525 3159243128775386220154697)
                    ·
                      refine ⟨2369432346581539665116023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159243128775386220154697 2369432346581539665116023)
                      ·
                        rfl

theorem cell23_4614453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_4614453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614453 prefixEnd_4614453 := by exact prefixLift 4614453
  have htrace : WordTrace (prefixWord ++ tailWord_4614453) baseStart_4614453 baseEnd_4614453 := by
    simpa [prefixWord, tailWord_4614453, baseEnd_4614453] using wordTrace_append hprefix tailTrace_4614453
  have hstable : (prefixWord ++ tailWord_4614453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614453).length < 2 ^ (prefixWord ++ tailWord_4614453).sum := by decide
  have hdescent : baseEnd_4614453 < baseStart_4614453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614523 : List Nat := [1, 1, 1, 1, 1, 7, 3, 3, 5]
def baseStart_4614523 : Nat := 118140960795 + 4614523 * 2 ^ 59
def prefixEnd_4614523 : Nat := 4983230072969 + 3 ^ 40 * 4614523 * 2
def baseEnd_4614523 : Nat := 263274254469706043471189

theorem tailTrace_4614523 : CollatzResearch.WordTrace tailWord_4614523 prefixEnd_4614523 263274254469706043471189 := by
  unfold tailWord_4614523
  simp only [CollatzResearch.WordTrace]
  refine ⟨168305480661378743629840223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112203653774252495753226815 168305480661378743629840223)
  ·
    refine ⟨252458220992068115444760335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168305480661378743629840223 252458220992068115444760335)
    ·
      refine ⟨378687331488102173167140503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252458220992068115444760335 378687331488102173167140503)
      ·
        refine ⟨568030997232153259750710755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378687331488102173167140503 568030997232153259750710755)
        ·
          refine ⟨852046495848229889626066133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568030997232153259750710755 852046495848229889626066133)
          ·
            refine ⟨19969839746442888038110925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 852046495848229889626066133 19969839746442888038110925)
            ·
              refine ⟨7488689904916083014291597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19969839746442888038110925 7488689904916083014291597)
              ·
                refine ⟨2808258714343531130359349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7488689904916083014291597 2808258714343531130359349)
                ·
                  refine ⟨263274254469706043471189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2808258714343531130359349 263274254469706043471189)
                  ·
                    rfl

theorem cell23_4614523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 5].length) (baseStart_4614523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614523 prefixEnd_4614523 := by exact prefixLift 4614523
  have htrace : WordTrace (prefixWord ++ tailWord_4614523) baseStart_4614523 baseEnd_4614523 := by
    simpa [prefixWord, tailWord_4614523, baseEnd_4614523] using wordTrace_append hprefix tailTrace_4614523
  have hstable : (prefixWord ++ tailWord_4614523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614523).length < 2 ^ (prefixWord ++ tailWord_4614523).sum := by decide
  have hdescent : baseEnd_4614523 < baseStart_4614523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614540 : List Nat := [2, 2, 1, 2, 1, 5, 3, 2, 5]
def baseStart_4614540 : Nat := 118140960795 + 4614540 * 2 ^ 59
def prefixEnd_4614540 : Nat := 4983230072969 + 3 ^ 40 * 4614540 * 2
def baseEnd_4614540 : Nat := 263275224377608980525347

theorem tailTrace_4614540 : CollatzResearch.WordTrace tailWord_4614540 prefixEnd_4614540 263275224377608980525347 := by
  unfold tailWord_4614540
  simp only [CollatzResearch.WordTrace]
  refine ⟨84153050351158577766604537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112204067134878103688806049 84153050351158577766604537)
  ·
    refine ⟨63114787763368933324953403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84153050351158577766604537 63114787763368933324953403)
    ·
      refine ⟨94672181645053399987430105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63114787763368933324953403 94672181645053399987430105)
      ·
        refine ⟨71004136233790049990572579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94672181645053399987430105 71004136233790049990572579)
        ·
          refine ⟨106506204350685074985858869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71004136233790049990572579 106506204350685074985858869)
          ·
            refine ⟨9984956657876725779924269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106506204350685074985858869 9984956657876725779924269)
            ·
              refine ⟨3744358746703772167471601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9984956657876725779924269 3744358746703772167471601)
              ·
                refine ⟨2808269060027829125603701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744358746703772167471601 2808269060027829125603701)
                ·
                  refine ⟨263275224377608980525347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2808269060027829125603701 263275224377608980525347)
                  ·
                    rfl

theorem cell23_4614540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_4614540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614540 prefixEnd_4614540 := by exact prefixLift 4614540
  have htrace : WordTrace (prefixWord ++ tailWord_4614540) baseStart_4614540 baseEnd_4614540 := by
    simpa [prefixWord, tailWord_4614540, baseEnd_4614540] using wordTrace_append hprefix tailTrace_4614540
  have hstable : (prefixWord ++ tailWord_4614540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614540).length < 2 ^ (prefixWord ++ tailWord_4614540).sum := by decide
  have hdescent : baseEnd_4614540 < baseStart_4614540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614576 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 3]
def baseStart_4614576 : Nat := 118140960795 + 4614576 * 2 ^ 59
def prefixEnd_4614576 : Nat := 4983230072969 + 3 ^ 40 * 4614576 * 2
def baseEnd_4614576 : Nat := 2369495504702042683877957

theorem tailTrace_4614576 : CollatzResearch.WordTrace tailWord_4614576 prefixEnd_4614576 2369495504702042683877957 := by
  unfold tailWord_4614576
  simp only [CollatzResearch.WordTrace]
  refine ⟨84153706865093366840759791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112204942486791155787679721 84153706865093366840759791)
  ·
    refine ⟨126230560297640050261139687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84153706865093366840759791 126230560297640050261139687)
    ·
      refine ⟨189345840446460075391709531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126230560297640050261139687 189345840446460075391709531)
      ·
        refine ⟨284018760669690113087564297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189345840446460075391709531 284018760669690113087564297)
        ·
          refine ⟨213014070502267584815673223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284018760669690113087564297 213014070502267584815673223)
          ·
            refine ⟨319521105753401377223509835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213014070502267584815673223 319521105753401377223509835)
            ·
              refine ⟨479281658630102065835264753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319521105753401377223509835 479281658630102065835264753)
              ·
                refine ⟨359461243972576549376448565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479281658630102065835264753 359461243972576549376448565)
                ·
                  refine ⟨33699491622429051504042053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 359461243972576549376448565 33699491622429051504042053)
                  ·
                    refine ⟨6318654679205447157007885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33699491622429051504042053 6318654679205447157007885)
                    ·
                      refine ⟨2369495504702042683877957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6318654679205447157007885 2369495504702042683877957)
                      ·
                        rfl

theorem cell23_4614576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 3].length) (baseStart_4614576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614576 prefixEnd_4614576 := by exact prefixLift 4614576
  have htrace : WordTrace (prefixWord ++ tailWord_4614576) baseStart_4614576 baseEnd_4614576 := by
    simpa [prefixWord, tailWord_4614576, baseEnd_4614576] using wordTrace_append hprefix tailTrace_4614576
  have hstable : (prefixWord ++ tailWord_4614576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614576).length < 2 ^ (prefixWord ++ tailWord_4614576).sum := by decide
  have hdescent : baseEnd_4614576 < baseStart_4614576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614613 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 6]
def baseStart_4614613 : Nat := 118140960795 + 4614613 * 2 ^ 59
def prefixEnd_4614613 : Nat := 4983230072969 + 3 ^ 40 * 4614613 * 2
def baseEnd_4614613 : Nat := 263279389276251004346143

theorem tailTrace_4614613 : CollatzResearch.WordTrace tailWord_4614613 prefixEnd_4614613 263279389276251004346143 := by
  unfold tailWord_4614613
  simp only [CollatzResearch.WordTrace]
  refine ⟨168308763231052689000616493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112205842154035126000410995 168308763231052689000616493)
  ·
    refine ⟨63115786211644758375231185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168308763231052689000616493 63115786211644758375231185)
    ·
      refine ⟨47336839658733568781423389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63115786211644758375231185 47336839658733568781423389)
      ·
        refine ⟨17751314872025088293033771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47336839658733568781423389 17751314872025088293033771)
        ·
          refine ⟨26626972308037632439550657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17751314872025088293033771 26626972308037632439550657)
          ·
            refine ⟨19970229231028224329662993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26626972308037632439550657 19970229231028224329662993)
            ·
              refine ⟨14977671923271168247247245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19970229231028224329662993 14977671923271168247247245)
              ·
                refine ⟨5616626971226688092717717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14977671923271168247247245 5616626971226688092717717)
                ·
                  refine ⟨263279389276251004346143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5616626971226688092717717 263279389276251004346143)
                  ·
                    rfl

theorem cell23_4614613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_4614613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614613 prefixEnd_4614613 := by exact prefixLift 4614613
  have htrace : WordTrace (prefixWord ++ tailWord_4614613) baseStart_4614613 baseEnd_4614613 := by
    simpa [prefixWord, tailWord_4614613, baseEnd_4614613] using wordTrace_append hprefix tailTrace_4614613
  have hstable : (prefixWord ++ tailWord_4614613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614613).length < 2 ^ (prefixWord ++ tailWord_4614613).sum := by decide
  have hdescent : baseEnd_4614613 < baseStart_4614613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614627 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 2, 2, 3]
def baseStart_4614627 : Nat := 118140960795 + 4614627 * 2 ^ 59
def prefixEnd_4614627 : Nat := 4983230072969 + 3 ^ 40 * 4614627 * 2
def baseEnd_4614627 : Nat := 2369521692215421984340223

theorem tailTrace_4614627 : CollatzResearch.WordTrace tailWord_4614627 prefixEnd_4614627 2369521692215421984340223 := by
  unfold tailWord_4614627
  simp only [CollatzResearch.WordTrace]
  refine ⟨168309273853001969391626135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112206182568667979594417423 168309273853001969391626135)
  ·
    refine ⟨252463910779502954087439203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168309273853001969391626135 252463910779502954087439203)
    ·
      refine ⟨378695866169254431131158805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252463910779502954087439203 378695866169254431131158805)
      ·
        refine ⟨17751368726683801459273069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 378695866169254431131158805 17751368726683801459273069)
        ·
          refine ⟨6656763272506425547227401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17751368726683801459273069 6656763272506425547227401)
          ·
            refine ⟨4992572454379819160420551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6656763272506425547227401 4992572454379819160420551)
            ·
              refine ⟨7488858681569728740630827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4992572454379819160420551 7488858681569728740630827)
              ·
                refine ⟨11233288022354593110946241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7488858681569728740630827 11233288022354593110946241)
                ·
                  refine ⟨8424966016765944833209681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11233288022354593110946241 8424966016765944833209681)
                  ·
                    refine ⟨6318724512574458624907261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8424966016765944833209681 6318724512574458624907261)
                    ·
                      refine ⟨2369521692215421984340223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6318724512574458624907261 2369521692215421984340223)
                      ·
                        rfl

theorem cell23_4614627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_4614627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614627 prefixEnd_4614627 := by exact prefixLift 4614627
  have htrace : WordTrace (prefixWord ++ tailWord_4614627) baseStart_4614627 baseEnd_4614627 := by
    simpa [prefixWord, tailWord_4614627, baseEnd_4614627] using wordTrace_append hprefix tailTrace_4614627
  have hstable : (prefixWord ++ tailWord_4614627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614627).length < 2 ^ (prefixWord ++ tailWord_4614627).sum := by decide
  have hdescent : baseEnd_4614627 < baseStart_4614627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614643 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 1, 5]
def baseStart_4614643 : Nat := 118140960795 + 4614643 * 2 ^ 59
def prefixEnd_4614643 : Nat := 4983230072969 + 3 ^ 40 * 4614643 * 2
def baseEnd_4614643 : Nat := 789843302635297973913383

theorem tailTrace_4614643 : CollatzResearch.WordTrace tailWord_4614643 prefixEnd_4614643 789843302635297973913383 := by
  unfold tailWord_4614643
  simp only [CollatzResearch.WordTrace]
  refine ⟨168309857420944004124208583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112206571613962669416139055 168309857420944004124208583)
  ·
    refine ⟨252464786131416006186312875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168309857420944004124208583 252464786131416006186312875)
    ·
      refine ⟨378697179197124009279469313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252464786131416006186312875 378697179197124009279469313)
      ·
        refine ⟨284022884397843006959601985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378697179197124009279469313 284022884397843006959601985)
        ·
          refine ⟨213017163298382255219701489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284022884397843006959601985 213017163298382255219701489)
          ·
            refine ⟨159762872473786691414776117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213017163298382255219701489 159762872473786691414776117)
            ·
              refine ⟨14977769294417502320135261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159762872473786691414776117 14977769294417502320135261)
              ·
                refine ⟨5616663485406563370050723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14977769294417502320135261 5616663485406563370050723)
                ·
                  refine ⟨8424995228109845055076085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5616663485406563370050723 8424995228109845055076085)
                  ·
                    refine ⟨789843302635297973913383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8424995228109845055076085 789843302635297973913383)
                    ·
                      rfl

theorem cell23_4614643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 5].length) (baseStart_4614643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614643 prefixEnd_4614643 := by exact prefixLift 4614643
  have htrace : WordTrace (prefixWord ++ tailWord_4614643) baseStart_4614643 baseEnd_4614643 := by
    simpa [prefixWord, tailWord_4614643, baseEnd_4614643] using wordTrace_append hprefix tailTrace_4614643
  have hstable : (prefixWord ++ tailWord_4614643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614643).length < 2 ^ (prefixWord ++ tailWord_4614643).sum := by decide
  have hdescent : baseEnd_4614643 < baseStart_4614643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614657 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_4614657 : Nat := 118140960795 + 4614657 * 2 ^ 59
def prefixEnd_4614657 : Nat := 4983230072969 + 3 ^ 40 * 4614657 * 2
def baseEnd_4614657 : Nat := 2369537096635056866965085

theorem tailTrace_4614657 : CollatzResearch.WordTrace tailWord_4614657 prefixEnd_4614657 2369537096635056866965085 := by
  unfold tailWord_4614657
  simp only [CollatzResearch.WordTrace]
  refine ⟨168310368042893284515218225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112206912028595523010145483 168310368042893284515218225)
  ·
    refine ⟨126232776032169963386413669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168310368042893284515218225 126232776032169963386413669)
    ·
      refine ⟨23668645506031868134952563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126232776032169963386413669 23668645506031868134952563)
      ·
        refine ⟨35502968259047802202428845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23668645506031868134952563 35502968259047802202428845)
        ·
          refine ⟨13313613097142925825910817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35502968259047802202428845 13313613097142925825910817)
          ·
            refine ⟨9985209822857194369433113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13313613097142925825910817 9985209822857194369433113)
            ·
              refine ⟨7488907367142895777074835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9985209822857194369433113 7488907367142895777074835)
              ·
                refine ⟨11233361050714343665612253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7488907367142895777074835 11233361050714343665612253)
                ·
                  refine ⟨4212510394017878874604595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11233361050714343665612253 4212510394017878874604595)
                  ·
                    refine ⟨6318765591026818311906893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4212510394017878874604595 6318765591026818311906893)
                    ·
                      refine ⟨2369537096635056866965085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6318765591026818311906893 2369537096635056866965085)
                      ·
                        rfl

theorem cell23_4614657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_4614657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614657 prefixEnd_4614657 := by exact prefixLift 4614657
  have htrace : WordTrace (prefixWord ++ tailWord_4614657) baseStart_4614657 baseEnd_4614657 := by
    simpa [prefixWord, tailWord_4614657, baseEnd_4614657] using wordTrace_append hprefix tailTrace_4614657
  have hstable : (prefixWord ++ tailWord_4614657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614657).length < 2 ^ (prefixWord ++ tailWord_4614657).sum := by decide
  have hdescent : baseEnd_4614657 < baseStart_4614657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614680 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 1, 1, 4]
def baseStart_4614680 : Nat := 118140960795 + 4614680 * 2 ^ 59
def prefixEnd_4614680 : Nat := 4983230072969 + 3 ^ 40 * 4614680 * 2
def baseEnd_4614680 : Nat := 2369548906690110276977479

theorem tailTrace_4614680 : CollatzResearch.WordTrace tailWord_4614680 prefixEnd_4614680 2369548906690110276977479 := by
  unfold tailWord_4614680
  simp only [CollatzResearch.WordTrace]
  refine ⟨84155603460904979721652747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112207471281206639628870329 84155603460904979721652747)
  ·
    refine ⟨126233405191357469582479121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84155603460904979721652747 126233405191357469582479121)
    ·
      refine ⟨94675053893518102186859341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126233405191357469582479121 94675053893518102186859341)
      ·
        refine ⟨35503145210069288320072253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94675053893518102186859341 35503145210069288320072253)
        ·
          refine ⟨13313679453775983120027095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35503145210069288320072253 13313679453775983120027095)
          ·
            refine ⟨19970519180663974680040643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13313679453775983120027095 19970519180663974680040643)
            ·
              refine ⟨29955778770995962020060965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19970519180663974680040643 29955778770995962020060965)
              ·
                refine ⟨5616708519561742878761431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29955778770995962020060965 5616708519561742878761431)
                ·
                  refine ⟨8425062779342614318142147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5616708519561742878761431 8425062779342614318142147)
                  ·
                    refine ⟨12637594169013921477213221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8425062779342614318142147 12637594169013921477213221)
                    ·
                      refine ⟨2369548906690110276977479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12637594169013921477213221 2369548906690110276977479)
                      ·
                        rfl

theorem cell23_4614680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_4614680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614680 prefixEnd_4614680 := by exact prefixLift 4614680
  have htrace : WordTrace (prefixWord ++ tailWord_4614680) baseStart_4614680 baseEnd_4614680 := by
    simpa [prefixWord, tailWord_4614680, baseEnd_4614680] using wordTrace_append hprefix tailTrace_4614680
  have hstable : (prefixWord ++ tailWord_4614680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614680).length < 2 ^ (prefixWord ++ tailWord_4614680).sum := by decide
  have hdescent : baseEnd_4614680 < baseStart_4614680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614693 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_4614693 : Nat := 118140960795 + 4614693 * 2 ^ 59
def prefixEnd_4614693 : Nat := 4983230072969 + 3 ^ 40 * 4614693 * 2
def baseEnd_4614693 : Nat := 2369555581938618726114919

theorem tailTrace_4614693 : CollatzResearch.WordTrace tailWord_4614693 prefixEnd_4614693 2369555581938618726114919 := by
  unfold tailWord_4614693
  simp only [CollatzResearch.WordTrace]
  refine ⟨168311681070762862663528733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112207787380508575109019155 168311681070762862663528733)
  ·
    refine ⟨63116880401536073498823275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168311681070762862663528733 63116880401536073498823275)
    ·
      refine ⟨94675320602304110248234913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63116880401536073498823275 94675320602304110248234913)
      ·
        refine ⟨71006490451728082686176185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94675320602304110248234913 71006490451728082686176185)
        ·
          refine ⟨53254867838796062014632139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71006490451728082686176185 53254867838796062014632139)
          ·
            refine ⟨79882301758194093021948209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53254867838796062014632139 79882301758194093021948209)
            ·
              refine ⟨59911726318645569766461157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79882301758194093021948209 59911726318645569766461157)
              ·
                refine ⟨11233448684746044331211467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59911726318645569766461157 11233448684746044331211467)
                ·
                  refine ⟨16850173027119066496817201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11233448684746044331211467 16850173027119066496817201)
                  ·
                    refine ⟨12637629770339299872612901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16850173027119066496817201 12637629770339299872612901)
                    ·
                      refine ⟨2369555581938618726114919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12637629770339299872612901 2369555581938618726114919)
                      ·
                        rfl

theorem cell23_4614693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_4614693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614693 prefixEnd_4614693 := by exact prefixLift 4614693
  have htrace : WordTrace (prefixWord ++ tailWord_4614693) baseStart_4614693 baseEnd_4614693 := by
    simpa [prefixWord, tailWord_4614693, baseEnd_4614693] using wordTrace_append hprefix tailTrace_4614693
  have hstable : (prefixWord ++ tailWord_4614693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614693).length < 2 ^ (prefixWord ++ tailWord_4614693).sum := by decide
  have hdescent : baseEnd_4614693 < baseStart_4614693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614708 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4614708 : Nat := 118140960795 + 4614708 * 2 ^ 59
def prefixEnd_4614708 : Nat := 4983230072969 + 3 ^ 40 * 4614708 * 2
def baseEnd_4614708 : Nat := 2369563284148436167427351

theorem tailTrace_4614708 : CollatzResearch.WordTrace tailWord_4614708 prefixEnd_4614708 2369563284148436167427351 := by
  unfold tailWord_4614708
  simp only [CollatzResearch.WordTrace]
  refine ⟨84156114082854260112662389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112208152110472346816883185 84156114082854260112662389)
  ·
    refine ⟨7889635695267586885562099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84156114082854260112662389 7889635695267586885562099)
    ·
      refine ⟨11834453542901380328343149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7889635695267586885562099 11834453542901380328343149)
      ·
        refine ⟨4437920078588017623128681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11834453542901380328343149 4437920078588017623128681)
        ·
          refine ⟨3328440058941013217346511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4437920078588017623128681 3328440058941013217346511)
          ·
            refine ⟨4992660088411519826019767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3328440058941013217346511 4992660088411519826019767)
            ·
              refine ⟨7488990132617279739029651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4992660088411519826019767 7488990132617279739029651)
              ·
                refine ⟨11233485198925919608544477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7488990132617279739029651 11233485198925919608544477)
                ·
                  refine ⟨4212556949597219853204179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11233485198925919608544477 4212556949597219853204179)
                  ·
                    refine ⟨6318835424395829779806269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4212556949597219853204179 6318835424395829779806269)
                    ·
                      refine ⟨2369563284148436167427351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6318835424395829779806269 2369563284148436167427351)
                      ·
                        rfl

theorem cell23_4614708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4614708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614708 prefixEnd_4614708 := by exact prefixLift 4614708
  have htrace : WordTrace (prefixWord ++ tailWord_4614708) baseStart_4614708 baseEnd_4614708 := by
    simpa [prefixWord, tailWord_4614708, baseEnd_4614708] using wordTrace_append hprefix tailTrace_4614708
  have hstable : (prefixWord ++ tailWord_4614708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614708).length < 2 ^ (prefixWord ++ tailWord_4614708).sum := by decide
  have hdescent : baseEnd_4614708 < baseStart_4614708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614710 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_4614710 : Nat := 118140960795 + 4614710 * 2 ^ 59
def prefixEnd_4614710 : Nat := 4983230072969 + 3 ^ 40 * 4614710 * 2
def baseEnd_4614710 : Nat := 2369564311109745159602341

theorem tailTrace_4614710 : CollatzResearch.WordTrace tailWord_4614710 prefixEnd_4614710 2369564311109745159602341 := by
  unfold tailWord_4614710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10519518819481329660431099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112208200741134183044598389 10519518819481329660431099)
  ·
    refine ⟨15779278229221994490646649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10519518819481329660431099 15779278229221994490646649)
    ·
      refine ⟨11834458671916495867984987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15779278229221994490646649 11834458671916495867984987)
      ·
        refine ⟨17751688007874743801977481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11834458671916495867984987 17751688007874743801977481)
        ·
          refine ⟨13313766005906057851483111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17751688007874743801977481 13313766005906057851483111)
          ·
            refine ⟨19970649008859086777224667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13313766005906057851483111 19970649008859086777224667)
            ·
              refine ⟨29955973513288630165837001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19970649008859086777224667 29955973513288630165837001)
              ·
                refine ⟨22466980134966472624377751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29955973513288630165837001 22466980134966472624377751)
                ·
                  refine ⟨33700470202449708936566627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22466980134966472624377751 33700470202449708936566627)
                  ·
                    refine ⟨50550705303674563404849941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33700470202449708936566627 50550705303674563404849941)
                    ·
                      refine ⟨2369564311109745159602341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50550705303674563404849941 2369564311109745159602341)
                      ·
                        rfl

theorem cell23_4614710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_4614710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614710 prefixEnd_4614710 := by exact prefixLift 4614710
  have htrace : WordTrace (prefixWord ++ tailWord_4614710) baseStart_4614710 baseEnd_4614710 := by
    simpa [prefixWord, tailWord_4614710, baseEnd_4614710] using wordTrace_append hprefix tailTrace_4614710
  have hstable : (prefixWord ++ tailWord_4614710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614710).length < 2 ^ (prefixWord ++ tailWord_4614710).sum := by decide
  have hdescent : baseEnd_4614710 < baseStart_4614710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614714 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2]
def baseStart_4614714 : Nat := 118140960795 + 4614714 * 2 ^ 59
def prefixEnd_4614714 : Nat := 4983230072969 + 3 ^ 40 * 4614714 * 2
def baseEnd_4614714 : Nat := 2369566365032363143952323

theorem tailTrace_4614714 : CollatzResearch.WordTrace tailWord_4614714 prefixEnd_4614714 2369566365032363143952323 := by
  unfold tailWord_4614714
  simp only [CollatzResearch.WordTrace]
  refine ⟨42078111750921695812510799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112208298002457855500028797 42078111750921695812510799)
  ·
    refine ⟨63117167626382543718766199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42078111750921695812510799 63117167626382543718766199)
    ·
      refine ⟨94675751439573815578149299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63117167626382543718766199 94675751439573815578149299)
      ·
        refine ⟨142013627159360723367223949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94675751439573815578149299 142013627159360723367223949)
        ·
          refine ⟨53255110184760271262708981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142013627159360723367223949 53255110184760271262708981)
          ·
            refine ⟨4992666579821275430878967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53255110184760271262708981 4992666579821275430878967)
            ·
              refine ⟨7488999869731913146318451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4992666579821275430878967 7488999869731913146318451)
              ·
                refine ⟨11233499804597869719477677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7488999869731913146318451 11233499804597869719477677)
                ·
                  refine ⟨4212562426724201144804129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11233499804597869719477677 4212562426724201144804129)
                  ·
                    refine ⟨3159421820043150858603097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4212562426724201144804129 3159421820043150858603097)
                    ·
                      refine ⟨2369566365032363143952323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159421820043150858603097 2369566365032363143952323)
                      ·
                        rfl

theorem cell23_4614714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_4614714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614714 prefixEnd_4614714 := by exact prefixLift 4614714
  have htrace : WordTrace (prefixWord ++ tailWord_4614714) baseStart_4614714 baseEnd_4614714 := by
    simpa [prefixWord, tailWord_4614714, baseEnd_4614714] using wordTrace_append hprefix tailTrace_4614714
  have hstable : (prefixWord ++ tailWord_4614714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614714).length < 2 ^ (prefixWord ++ tailWord_4614714).sum := by decide
  have hdescent : baseEnd_4614714 < baseStart_4614714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614804 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_4614804 : Nat := 118140960795 + 4614804 * 2 ^ 59
def prefixEnd_4614804 : Nat := 4983230072969 + 3 ^ 40 * 4614804 * 2
def baseEnd_4614804 : Nat := 2369612578291267791826909

theorem tailTrace_4614804 : CollatzResearch.WordTrace tailWord_4614804 prefixEnd_4614804 2369612578291267791826909 := by
  unfold tailWord_4614804
  simp only [CollatzResearch.WordTrace]
  refine ⟨84157864786680364310409733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112210486382240485747212977 84157864786680364310409733)
  ·
    refine ⟨15779599647502568308201825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84157864786680364310409733 15779599647502568308201825)
    ·
      refine ⟨11834699735626926231151369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15779599647502568308201825 11834699735626926231151369)
      ·
        refine ⟨8876024801720194673363527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11834699735626926231151369 8876024801720194673363527)
        ·
          refine ⟨13314037202580292010045291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8876024801720194673363527 13314037202580292010045291)
          ·
            refine ⟨19971055803870438015067937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13314037202580292010045291 19971055803870438015067937)
            ·
              refine ⟨14978291852902828511300953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19971055803870438015067937 14978291852902828511300953)
              ·
                refine ⟨11233718889677121383475715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14978291852902828511300953 11233718889677121383475715)
                ·
                  refine ⟨16850578334515682075213573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11233718889677121383475715 16850578334515682075213573)
                  ·
                    refine ⟨3159483437721690389102545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16850578334515682075213573 3159483437721690389102545)
                    ·
                      refine ⟨2369612578291267791826909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159483437721690389102545 2369612578291267791826909)
                      ·
                        rfl

theorem cell23_4614804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_4614804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614804 prefixEnd_4614804 := by exact prefixLift 4614804
  have htrace : WordTrace (prefixWord ++ tailWord_4614804) baseStart_4614804 baseEnd_4614804 := by
    simpa [prefixWord, tailWord_4614804, baseEnd_4614804] using wordTrace_append hprefix tailTrace_4614804
  have hstable : (prefixWord ++ tailWord_4614804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614804).length < 2 ^ (prefixWord ++ tailWord_4614804).sum := by decide
  have hdescent : baseEnd_4614804 < baseStart_4614804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614820 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_4614820 : Nat := 118140960795 + 4614820 * 2 ^ 59
def prefixEnd_4614820 : Nat := 4983230072969 + 3 ^ 40 * 4614820 * 2
def baseEnd_4614820 : Nat := 2369620793981739729226835

theorem tailTrace_4614820 : CollatzResearch.WordTrace tailWord_4614820 prefixEnd_4614820 2369620793981739729226835 := by
  unfold tailWord_4614820
  simp only [CollatzResearch.WordTrace]
  refine ⟨84158156570651381676700957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112210875427535175568934609 84158156570651381676700957)
  ·
    refine ⟨31559308713994268128762859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84158156570651381676700957 31559308713994268128762859)
    ·
      refine ⟨47338963070991402193144289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31559308713994268128762859 47338963070991402193144289)
      ·
        refine ⟨35504222303243551644858217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47338963070991402193144289 35504222303243551644858217)
        ·
          refine ⟨26628166727432663733643663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35504222303243551644858217 26628166727432663733643663)
          ·
            refine ⟨39942250091148995600465495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26628166727432663733643663 39942250091148995600465495)
            ·
              refine ⟨59913375136723493400698243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39942250091148995600465495 59913375136723493400698243)
              ·
                refine ⟨89870062705085240101047365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59913375136723493400698243 89870062705085240101047365)
                ·
                  refine ⟨16850636757203482518946381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89870062705085240101047365 16850636757203482518946381)
                  ·
                    refine ⟨6318988783951305944604893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16850636757203482518946381 6318988783951305944604893)
                    ·
                      refine ⟨2369620793981739729226835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6318988783951305944604893 2369620793981739729226835)
                      ·
                        rfl

theorem cell23_4614820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_4614820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614820 prefixEnd_4614820 := by exact prefixLift 4614820
  have htrace : WordTrace (prefixWord ++ tailWord_4614820) baseStart_4614820 baseEnd_4614820 := by
    simpa [prefixWord, tailWord_4614820, baseEnd_4614820] using wordTrace_append hprefix tailTrace_4614820
  have hstable : (prefixWord ++ tailWord_4614820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614820).length < 2 ^ (prefixWord ++ tailWord_4614820).sum := by decide
  have hdescent : baseEnd_4614820 < baseStart_4614820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614837 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_4614837 : Nat := 118140960795 + 4614837 * 2 ^ 59
def prefixEnd_4614837 : Nat := 4983230072969 + 3 ^ 40 * 4614837 * 2
def baseEnd_4614837 : Nat := 2369629523152866162714257

theorem tailTrace_4614837 : CollatzResearch.WordTrace tailWord_4614837 prefixEnd_4614837 2369629523152866162714257 := by
  unfold tailWord_4614837
  simp only [CollatzResearch.WordTrace]
  refine ⟨168316933182241175256770765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112211288788160783504513843 168316933182241175256770765)
  ·
    refine ⟨63118849943340440721289037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168316933182241175256770765 63118849943340440721289037)
    ·
      refine ⟨23669568728752665270483389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63118849943340440721289037 23669568728752665270483389)
      ·
        refine ⟨8876088273282249476431271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23669568728752665270483389 8876088273282249476431271)
        ·
          refine ⟨13314132409923374214646907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8876088273282249476431271 13314132409923374214646907)
          ·
            refine ⟨19971198614885061321970361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13314132409923374214646907 19971198614885061321970361)
            ·
              refine ⟨14978398961163795991477771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19971198614885061321970361 14978398961163795991477771)
              ·
                refine ⟨22467598441745693987216657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14978398961163795991477771 22467598441745693987216657)
                ·
                  refine ⟨16850698831309270490412493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22467598441745693987216657 16850698831309270490412493)
                  ·
                    refine ⟨6319012061740976433904685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16850698831309270490412493 6319012061740976433904685)
                    ·
                      refine ⟨2369629523152866162714257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6319012061740976433904685 2369629523152866162714257)
                      ·
                        rfl

theorem cell23_4614837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_4614837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614837 prefixEnd_4614837 := by exact prefixLift 4614837
  have htrace : WordTrace (prefixWord ++ tailWord_4614837) baseStart_4614837 baseEnd_4614837 := by
    simpa [prefixWord, tailWord_4614837, baseEnd_4614837] using wordTrace_append hprefix tailTrace_4614837
  have hstable : (prefixWord ++ tailWord_4614837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614837).length < 2 ^ (prefixWord ++ tailWord_4614837).sum := by decide
  have hdescent : baseEnd_4614837 < baseStart_4614837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614838 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_4614838 : Nat := 118140960795 + 4614838 * 2 ^ 59
def prefixEnd_4614838 : Nat := 4983230072969 + 3 ^ 40 * 4614838 * 2
def baseEnd_4614838 : Nat := 2369630036633520658801753

theorem tailTrace_4614838 : CollatzResearch.WordTrace tailWord_4614838 prefixEnd_4614838 2369630036633520658801753 := by
  unfold tailWord_4614838
  simp only [CollatzResearch.WordTrace]
  refine ⟨10519810603452347026722323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112211313103491701618371445 10519810603452347026722323)
  ·
    refine ⟨15779715905178520540083485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10519810603452347026722323 15779715905178520540083485)
    ·
      refine ⟨5917393464441945202531307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15779715905178520540083485 5917393464441945202531307)
      ·
        refine ⟨8876090196662917803796961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5917393464441945202531307 8876090196662917803796961)
        ·
          refine ⟨6657067647497188352847721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8876090196662917803796961 6657067647497188352847721)
          ·
            refine ⟨4992800735622891264635791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6657067647497188352847721 4992800735622891264635791)
            ·
              refine ⟨7489201103434336896953687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4992800735622891264635791 7489201103434336896953687)
              ·
                refine ⟨11233801655151505345430531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7489201103434336896953687 11233801655151505345430531)
                ·
                  refine ⟨16850702482727258018145797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11233801655151505345430531 16850702482727258018145797)
                  ·
                    refine ⟨3159506715511360878402337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16850702482727258018145797 3159506715511360878402337)
                    ·
                      refine ⟨2369630036633520658801753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159506715511360878402337 2369630036633520658801753)
                      ·
                        rfl

theorem cell23_4614838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_4614838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614838 prefixEnd_4614838 := by exact prefixLift 4614838
  have htrace : WordTrace (prefixWord ++ tailWord_4614838) baseStart_4614838 baseEnd_4614838 := by
    simpa [prefixWord, tailWord_4614838, baseEnd_4614838] using wordTrace_append hprefix tailTrace_4614838
  have hstable : (prefixWord ++ tailWord_4614838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614838).length < 2 ^ (prefixWord ++ tailWord_4614838).sum := by decide
  have hdescent : baseEnd_4614838 < baseStart_4614838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614863 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_4614863 : Nat := 118140960795 + 4614863 * 2 ^ 59
def prefixEnd_4614863 : Nat := 4983230072969 + 3 ^ 40 * 4614863 * 2
def baseEnd_4614863 : Nat := 2369642873649883060989137

theorem tailTrace_4614863 : CollatzResearch.WordTrace tailWord_4614863 prefixEnd_4614863 2369642873649883060989137 := by
  unfold tailWord_4614863
  simp only [CollatzResearch.WordTrace]
  refine ⟨168317881480146981697217243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112211920986764654464811495 168317881480146981697217243)
  ·
    refine ⟨252476822220220472545825865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168317881480146981697217243 252476822220220472545825865)
    ·
      refine ⟨189357616665165354409369399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252476822220220472545825865 189357616665165354409369399)
      ·
        refine ⟨284036424997748031614054099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189357616665165354409369399 284036424997748031614054099)
        ·
          refine ⟨426054637496622047421081149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284036424997748031614054099 426054637496622047421081149)
          ·
            refine ⟨159770489061233267782905431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 426054637496622047421081149 159770489061233267782905431)
            ·
              refine ⟨239655733591849901674358147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159770489061233267782905431 239655733591849901674358147)
              ·
                refine ⟨359483600387774852511537221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239655733591849901674358147 359483600387774852511537221)
                ·
                  refine ⟨67403175072707784845913229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 359483600387774852511537221 67403175072707784845913229)
                  ·
                    refine ⟨25276190652265419317217461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67403175072707784845913229 25276190652265419317217461)
                    ·
                      refine ⟨2369642873649883060989137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25276190652265419317217461 2369642873649883060989137)
                      ·
                        rfl

theorem cell23_4614863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_4614863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614863 prefixEnd_4614863 := by exact prefixLift 4614863
  have htrace : WordTrace (prefixWord ++ tailWord_4614863) baseStart_4614863 baseEnd_4614863 := by
    simpa [prefixWord, tailWord_4614863, baseEnd_4614863] using wordTrace_append hprefix tailTrace_4614863
  have hstable : (prefixWord ++ tailWord_4614863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614863).length < 2 ^ (prefixWord ++ tailWord_4614863).sum := by decide
  have hdescent : baseEnd_4614863 < baseStart_4614863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614914 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_4614914 : Nat := 118140960795 + 4614914 * 2 ^ 59
def prefixEnd_4614914 : Nat := 4983230072969 + 3 ^ 40 * 4614914 * 2
def baseEnd_4614914 : Nat := 2369669061163262361451403

theorem tailTrace_4614914 : CollatzResearch.WordTrace tailWord_4614914 prefixEnd_4614914 2369669061163262361451403 := by
  unfold tailWord_4614914
  simp only [CollatzResearch.WordTrace]
  refine ⟨42079935400740554351830949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112213161068641478271549197 42079935400740554351830949)
  ·
    refine ⟨7889987887638853940968303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42079935400740554351830949 7889987887638853940968303)
    ·
      refine ⟨11834981831458280911452455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7889987887638853940968303 11834981831458280911452455)
      ·
        refine ⟨17752472747187421367178683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11834981831458280911452455 17752472747187421367178683)
        ·
          refine ⟨26628709120781132050768025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17752472747187421367178683 26628709120781132050768025)
          ·
            refine ⟨19971531840585849038076019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26628709120781132050768025 19971531840585849038076019)
            ·
              refine ⟨29957297760878773557114029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19971531840585849038076019 29957297760878773557114029)
              ·
                refine ⟨11233986660329540083917761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29957297760878773557114029 11233986660329540083917761)
                ·
                  refine ⟨8425489995247155062938321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11233986660329540083917761 8425489995247155062938321)
                  ·
                    refine ⟨6319117496435366297203741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8425489995247155062938321 6319117496435366297203741)
                    ·
                      refine ⟨2369669061163262361451403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6319117496435366297203741 2369669061163262361451403)
                      ·
                        rfl

theorem cell23_4614914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_4614914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614914 prefixEnd_4614914 := by exact prefixLift 4614914
  have htrace : WordTrace (prefixWord ++ tailWord_4614914) baseStart_4614914 baseEnd_4614914 := by
    simpa [prefixWord, tailWord_4614914, baseEnd_4614914] using wordTrace_append hprefix tailTrace_4614914
  have hstable : (prefixWord ++ tailWord_4614914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614914).length < 2 ^ (prefixWord ++ tailWord_4614914).sum := by decide
  have hdescent : baseEnd_4614914 < baseStart_4614914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614937 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 4, 3, 2]
def baseStart_4614937 : Nat := 118140960795 + 4614937 * 2 ^ 59
def prefixEnd_4614937 : Nat := 4983230072969 + 3 ^ 40 * 4614937 * 2
def baseEnd_4614937 : Nat := 2369680871218315771463797

theorem tailTrace_4614937 : CollatzResearch.WordTrace tailWord_4614937 prefixEnd_4614937 2369680871218315771463797 := by
  unfold tailWord_4614937
  simp only [CollatzResearch.WordTrace]
  refine ⟨168320580481878892335411065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112213720321252594890274043 168320580481878892335411065)
  ·
    refine ⟨126240435361409169251558299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168320580481878892335411065 126240435361409169251558299)
    ·
      refine ⟨189360653042113753877337449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126240435361409169251558299 189360653042113753877337449)
      ·
        refine ⟨142020489781585315408003087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189360653042113753877337449 142020489781585315408003087)
        ·
          refine ⟨213030734672377973112004631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142020489781585315408003087 213030734672377973112004631)
          ·
            refine ⟨319546102008566959668006947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213030734672377973112004631 319546102008566959668006947)
            ·
              refine ⟨479319153012850439502010421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319546102008566959668006947 479319153012850439502010421)
              ·
                refine ⟨44936170594954728703313477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 479319153012850439502010421 44936170594954728703313477)
                ·
                  refine ⟨8425531986554011631871277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44936170594954728703313477 8425531986554011631871277)
                  ·
                    refine ⟨3159574494957754361951729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8425531986554011631871277 3159574494957754361951729)
                    ·
                      refine ⟨2369680871218315771463797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159574494957754361951729 2369680871218315771463797)
                      ·
                        rfl

theorem cell23_4614937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_4614937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614937 prefixEnd_4614937 := by exact prefixLift 4614937
  have htrace : WordTrace (prefixWord ++ tailWord_4614937) baseStart_4614937 baseEnd_4614937 := by
    simpa [prefixWord, tailWord_4614937, baseEnd_4614937] using wordTrace_append hprefix tailTrace_4614937
  have hstable : (prefixWord ++ tailWord_4614937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614937).length < 2 ^ (prefixWord ++ tailWord_4614937).sum := by decide
  have hdescent : baseEnd_4614937 < baseStart_4614937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614967 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 4]
def baseStart_4614967 : Nat := 118140960795 + 4614967 * 2 ^ 59
def prefixEnd_4614967 : Nat := 4983230072969 + 3 ^ 40 * 4614967 * 2
def baseEnd_4614967 : Nat := 2369696275637950654088659

theorem tailTrace_4614967 : CollatzResearch.WordTrace tailWord_4614967 prefixEnd_4614967 2369696275637950654088659 := by
  unfold tailWord_4614967
  simp only [CollatzResearch.WordTrace]
  refine ⟨168321674671770207459003155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112214449781180138306002103 168321674671770207459003155)
  ·
    refine ⟨252482512007655311188504733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168321674671770207459003155 252482512007655311188504733)
    ·
      refine ⟨94680942002870741695689275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252482512007655311188504733 94680942002870741695689275)
      ·
        refine ⟨142021413004306112543533913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94680942002870741695689275 142021413004306112543533913)
        ·
          refine ⟨106516059753229584407650435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142021413004306112543533913 106516059753229584407650435)
          ·
            refine ⟨159774089629844376611475653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106516059753229584407650435 159774089629844376611475653)
            ·
              refine ⟨29957641805595820614651685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159774089629844376611475653 29957641805595820614651685)
              ·
                refine ⟨5617057838549216365247191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29957641805595820614651685 5617057838549216365247191)
                ·
                  refine ⟨8425586757823824547870787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5617057838549216365247191 8425586757823824547870787)
                  ·
                    refine ⟨12638380136735736821806181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8425586757823824547870787 12638380136735736821806181)
                    ·
                      refine ⟨2369696275637950654088659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12638380136735736821806181 2369696275637950654088659)
                      ·
                        rfl

theorem cell23_4614967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_4614967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614967 prefixEnd_4614967 := by exact prefixLift 4614967
  have htrace : WordTrace (prefixWord ++ tailWord_4614967) baseStart_4614967 baseEnd_4614967 := by
    simpa [prefixWord, tailWord_4614967, baseEnd_4614967] using wordTrace_append hprefix tailTrace_4614967
  have hstable : (prefixWord ++ tailWord_4614967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614967).length < 2 ^ (prefixWord ++ tailWord_4614967).sum := by decide
  have hdescent : baseEnd_4614967 < baseStart_4614967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4614984 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 5, 2, 2]
def baseStart_4614984 : Nat := 118140960795 + 4614984 * 2 ^ 59
def prefixEnd_4614984 : Nat := 4983230072969 + 3 ^ 40 * 4614984 * 2
def baseEnd_4614984 : Nat := 2369705004809077087576081

theorem tailTrace_4614984 : CollatzResearch.WordTrace tailWord_4614984 prefixEnd_4614984 2369705004809077087576081 := by
  unfold tailWord_4614984
  simp only [CollatzResearch.WordTrace]
  refine ⟨84161147356354309681186003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112214863141805746241581337 84161147356354309681186003)
  ·
    refine ⟨126241721034531464521779005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84161147356354309681186003 126241721034531464521779005)
    ·
      refine ⟨47340645387949299195667127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126241721034531464521779005 47340645387949299195667127)
      ·
        refine ⟨71010968081923948793500691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47340645387949299195667127 71010968081923948793500691)
        ·
          refine ⟨106516452122885923190251037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71010968081923948793500691 106516452122885923190251037)
          ·
            refine ⟨39943669546082221196344139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106516452122885923190251037 39943669546082221196344139)
            ·
              refine ⟨59915504319123331794516209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39943669546082221196344139 59915504319123331794516209)
              ·
                refine ⟨44936628239342498845887157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59915504319123331794516209 44936628239342498845887157)
                ·
                  refine ⟨4212808897438359266801921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44936628239342498845887157 4212808897438359266801921)
                  ·
                    refine ⟨3159606673078769450101441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4212808897438359266801921 3159606673078769450101441)
                    ·
                      refine ⟨2369705004809077087576081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159606673078769450101441 2369705004809077087576081)
                      ·
                        rfl

theorem cell23_4614984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_4614984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4614984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4614984 prefixEnd_4614984 := by exact prefixLift 4614984
  have htrace : WordTrace (prefixWord ++ tailWord_4614984) baseStart_4614984 baseEnd_4614984 := by
    simpa [prefixWord, tailWord_4614984, baseEnd_4614984] using wordTrace_append hprefix tailTrace_4614984
  have hstable : (prefixWord ++ tailWord_4614984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4614984).length < 2 ^ (prefixWord ++ tailWord_4614984).sum := by decide
  have hdescent : baseEnd_4614984 < baseStart_4614984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4614984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615001 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 3, 2, 2]
def baseStart_4615001 : Nat := 118140960795 + 4615001 * 2 ^ 59
def prefixEnd_4615001 : Nat := 4983230072969 + 3 ^ 40 * 4615001 * 2
def baseEnd_4615001 : Nat := 2369713733980203521063503

theorem tailTrace_4615001 : CollatzResearch.WordTrace tailWord_4615001 prefixEnd_4615001 2369713733980203521063503 := by
  unfold tailWord_4615001
  simp only [CollatzResearch.WordTrace]
  refine ⟨168322914753647031265740857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112215276502431354177160571 168322914753647031265740857)
  ·
    refine ⟨126242186065235273449305643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168322914753647031265740857 126242186065235273449305643)
    ·
      refine ⟨189363279097852910173958465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126242186065235273449305643 189363279097852910173958465)
      ·
        refine ⟨142022459323389682630468849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189363279097852910173958465 142022459323389682630468849)
        ·
          refine ⟨106516844492542261972851637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142022459323389682630468849 106516844492542261972851637)
          ·
            refine ⟨9985954171175837059954841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106516844492542261972851637 9985954171175837059954841)
            ·
              refine ⟨7489465628381877794966131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9985954171175837059954841 7489465628381877794966131)
              ·
                refine ⟨11234198442572816692449197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7489465628381877794966131 11234198442572816692449197)
                ·
                  refine ⟨4212824415964806259668449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11234198442572816692449197 4212824415964806259668449)
                  ·
                    refine ⟨3159618311973604694751337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4212824415964806259668449 3159618311973604694751337)
                    ·
                      refine ⟨2369713733980203521063503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159618311973604694751337 2369713733980203521063503)
                      ·
                        rfl

theorem cell23_4615001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_4615001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615001 prefixEnd_4615001 := by exact prefixLift 4615001
  have htrace : WordTrace (prefixWord ++ tailWord_4615001) baseStart_4615001 baseEnd_4615001 := by
    simpa [prefixWord, tailWord_4615001, baseEnd_4615001] using wordTrace_append hprefix tailTrace_4615001
  have hstable : (prefixWord ++ tailWord_4615001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615001).length < 2 ^ (prefixWord ++ tailWord_4615001).sum := by decide
  have hdescent : baseEnd_4615001 < baseStart_4615001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615004 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4615004 : Nat := 118140960795 + 4615004 * 2 ^ 59
def prefixEnd_4615004 : Nat := 4983230072969 + 3 ^ 40 * 4615004 * 2
def baseEnd_4615004 : Nat := 2369715274422167009325989

theorem tailTrace_4615004 : CollatzResearch.WordTrace tailWord_4615004 prefixEnd_4615004 2369715274422167009325989 := by
  unfold tailWord_4615004
  simp only [CollatzResearch.WordTrace]
  refine ⟨84161512086318081389050033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112215349448424108518733377 84161512086318081389050033)
  ·
    refine ⟨63121134064738561041787525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84161512086318081389050033 63121134064738561041787525)
    ·
      refine ⟨11835212637138480195335161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63121134064738561041787525 11835212637138480195335161)
      ·
        refine ⟨8876409477853860146501371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11835212637138480195335161 8876409477853860146501371)
        ·
          refine ⟨13314614216780790219752057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8876409477853860146501371 13314614216780790219752057)
          ·
            refine ⟨9985960662585592664814043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13314614216780790219752057 9985960662585592664814043)
            ·
              refine ⟨14978940993878388997221065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9985960662585592664814043 14978940993878388997221065)
              ·
                refine ⟨11234205745408791747915799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14978940993878388997221065 11234205745408791747915799)
                ·
                  refine ⟨16851308618113187621873699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11234205745408791747915799 16851308618113187621873699)
                  ·
                    refine ⟨25276962927169781432810549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16851308618113187621873699 25276962927169781432810549)
                    ·
                      refine ⟨2369715274422167009325989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25276962927169781432810549 2369715274422167009325989)
                      ·
                        rfl

theorem cell23_4615004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4615004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615004 prefixEnd_4615004 := by exact prefixLift 4615004
  have htrace : WordTrace (prefixWord ++ tailWord_4615004) baseStart_4615004 baseEnd_4615004 := by
    simpa [prefixWord, tailWord_4615004, baseEnd_4615004] using wordTrace_append hprefix tailTrace_4615004
  have hstable : (prefixWord ++ tailWord_4615004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615004).length < 2 ^ (prefixWord ++ tailWord_4615004).sum := by decide
  have hdescent : baseEnd_4615004 < baseStart_4615004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615011 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 2, 4]
def baseStart_4615011 : Nat := 118140960795 + 4615011 * 2 ^ 59
def prefixEnd_4615011 : Nat := 4983230072969 + 3 ^ 40 * 4615011 * 2
def baseEnd_4615011 : Nat := 789906289595582827312819

theorem tailTrace_4615011 : CollatzResearch.WordTrace tailWord_4615011 prefixEnd_4615011 789906289595582827312819 := by
  unfold tailWord_4615011
  simp only [CollatzResearch.WordTrace]
  refine ⟨168323279483610802973604887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112215519655740535315736591 168323279483610802973604887)
  ·
    refine ⟨252484919225416204460407331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168323279483610802973604887 252484919225416204460407331)
    ·
      refine ⟨378727378838124306690610997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252484919225416204460407331 378727378838124306690610997)
      ·
        refine ⟨35505691766074153752244781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 378727378838124306690610997 35505691766074153752244781)
        ·
          refine ⟨13314634412277807657091793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35505691766074153752244781 13314634412277807657091793)
          ·
            refine ⟨9985975809208355742818845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13314634412277807657091793 9985975809208355742818845)
            ·
              refine ⟨3744740928453133403557067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9985975809208355742818845 3744740928453133403557067)
              ·
                refine ⟨5617111392679700105335601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3744740928453133403557067 5617111392679700105335601)
                ·
                  refine ⟨4212833544509775079001701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5617111392679700105335601 4212833544509775079001701)
                  ·
                    refine ⟨789906289595582827312819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4212833544509775079001701 789906289595582827312819)
                    ·
                      rfl

theorem cell23_4615011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 2, 4].length) (baseStart_4615011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615011 prefixEnd_4615011 := by exact prefixLift 4615011
  have htrace : WordTrace (prefixWord ++ tailWord_4615011) baseStart_4615011 baseEnd_4615011 := by
    simpa [prefixWord, tailWord_4615011, baseEnd_4615011] using wordTrace_append hprefix tailTrace_4615011
  have hstable : (prefixWord ++ tailWord_4615011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615011).length < 2 ^ (prefixWord ++ tailWord_4615011).sum := by decide
  have hdescent : baseEnd_4615011 < baseStart_4615011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615044 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_4615044 : Nat := 118140960795 + 4615044 * 2 ^ 59
def prefixEnd_4615044 : Nat := 4983230072969 + 3 ^ 40 * 4615044 * 2
def baseEnd_4615044 : Nat := 2369735813648346852825805

theorem tailTrace_4615044 : CollatzResearch.WordTrace tailWord_4615044 prefixEnd_4615044 2369735813648346852825805 := by
  unfold tailWord_4615044
  simp only [CollatzResearch.WordTrace]
  refine ⟨84162241546245624804778093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112216322061660833073037457 84162241546245624804778093)
  ·
    refine ⟨31560840579842109301791785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84162241546245624804778093 31560840579842109301791785)
    ·
      refine ⟨23670630434881581976343839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31560840579842109301791785 23670630434881581976343839)
      ·
        refine ⟨35505945652322372964515759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23670630434881581976343839 35505945652322372964515759)
        ·
          refine ⟨53258918478483559446773639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35505945652322372964515759 53258918478483559446773639)
          ·
            refine ⟨79888377717725339170160459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53258918478483559446773639 79888377717725339170160459)
            ·
              refine ⟨119832566576588008755240689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79888377717725339170160459 119832566576588008755240689)
              ·
                refine ⟨89874424932441006566430517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119832566576588008755240689 89874424932441006566430517)
                ·
                  refine ⟨8425727337416344365602861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89874424932441006566430517 8425727337416344365602861)
                  ·
                    refine ⟨3159647751531129137101073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8425727337416344365602861 3159647751531129137101073)
                    ·
                      refine ⟨2369735813648346852825805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159647751531129137101073 2369735813648346852825805)
                      ·
                        rfl

theorem cell23_4615044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_4615044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615044 prefixEnd_4615044 := by exact prefixLift 4615044
  have htrace : WordTrace (prefixWord ++ tailWord_4615044) baseStart_4615044 baseEnd_4615044 := by
    simpa [prefixWord, tailWord_4615044, baseEnd_4615044] using wordTrace_append hprefix tailTrace_4615044
  have hstable : (prefixWord ++ tailWord_4615044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615044).length < 2 ^ (prefixWord ++ tailWord_4615044).sum := by decide
  have hdescent : baseEnd_4615044 < baseStart_4615044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615062 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4615062 : Nat := 118140960795 + 4615062 * 2 ^ 59
def prefixEnd_4615062 : Nat := 4983230072969 + 3 ^ 40 * 4615062 * 2
def baseEnd_4615062 : Nat := 789915018766709260800241

theorem tailTrace_4615062 : CollatzResearch.WordTrace tailWord_4615062 prefixEnd_4615062 789915018766709260800241 := by
  unfold tailWord_4615062
  simp only [CollatzResearch.WordTrace]
  refine ⟨10520321225401627417731965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112216759737617359122474293 10520321225401627417731965)
  ·
    refine ⟨3945120459525610281649487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10520321225401627417731965 3945120459525610281649487)
    ·
      refine ⟨5917680689288415422474231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3945120459525610281649487 5917680689288415422474231)
      ·
        refine ⟨8876521033932623133711347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5917680689288415422474231 8876521033932623133711347)
        ·
          refine ⟨13314781550898934700567021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8876521033932623133711347 13314781550898934700567021)
          ·
            refine ⟨4993043081587100512712633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13314781550898934700567021 4993043081587100512712633)
            ·
              refine ⟨3744782311190325384534475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4993043081587100512712633 3744782311190325384534475)
              ·
                refine ⟨5617173466785488076801713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3744782311190325384534475 5617173466785488076801713)
                ·
                  refine ⟨4212880100089116057601285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5617173466785488076801713 4212880100089116057601285)
                  ·
                    refine ⟨789915018766709260800241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4212880100089116057601285 789915018766709260800241)
                    ·
                      rfl

theorem cell23_4615062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4615062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615062 prefixEnd_4615062 := by exact prefixLift 4615062
  have htrace : WordTrace (prefixWord ++ tailWord_4615062) baseStart_4615062 baseEnd_4615062 := by
    simpa [prefixWord, tailWord_4615062, baseEnd_4615062] using wordTrace_append hprefix tailTrace_4615062
  have hstable : (prefixWord ++ tailWord_4615062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615062).length < 2 ^ (prefixWord ++ tailWord_4615062).sum := by decide
  have hdescent : baseEnd_4615062 < baseStart_4615062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615068 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4615068 : Nat := 118140960795 + 4615068 * 2 ^ 59
def prefixEnd_4615068 : Nat := 4983230072969 + 3 ^ 40 * 4615068 * 2
def baseEnd_4615068 : Nat := 2369748137184054758925695

theorem tailTrace_4615068 : CollatzResearch.WordTrace tailWord_4615068 prefixEnd_4615068 2369748137184054758925695 := by
  unfold tailWord_4615068
  simp only [CollatzResearch.WordTrace]
  refine ⟨84162679222202150854214929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112216905629602867805619905 84162679222202150854214929)
  ·
    refine ⟨63122009416651613140661197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84162679222202150854214929 63122009416651613140661197)
    ·
      refine ⟨23670753531244354927747949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63122009416651613140661197 23670753531244354927747949)
      ·
        refine ⟨8876532574216633097905481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23670753531244354927747949 8876532574216633097905481)
        ·
          refine ⟨6657399430662474823429111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8876532574216633097905481 6657399430662474823429111)
          ·
            refine ⟨9986099145993712235143667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6657399430662474823429111 9986099145993712235143667)
            ·
              refine ⟨14979148718990568352715501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9986099145993712235143667 14979148718990568352715501)
              ·
                refine ⟨5617180769621463132268313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14979148718990568352715501 5617180769621463132268313)
                ·
                  refine ⟨4212885577216097349201235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5617180769621463132268313 4212885577216097349201235)
                  ·
                    refine ⟨6319328365824146023801853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4212885577216097349201235 6319328365824146023801853)
                    ·
                      refine ⟨2369748137184054758925695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6319328365824146023801853 2369748137184054758925695)
                      ·
                        rfl

theorem cell23_4615068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4615068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615068 prefixEnd_4615068 := by exact prefixLift 4615068
  have htrace : WordTrace (prefixWord ++ tailWord_4615068) baseStart_4615068 baseEnd_4615068 := by
    simpa [prefixWord, tailWord_4615068, baseEnd_4615068] using wordTrace_append hprefix tailTrace_4615068
  have hstable : (prefixWord ++ tailWord_4615068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615068).length < 2 ^ (prefixWord ++ tailWord_4615068).sum := by decide
  have hdescent : baseEnd_4615068 < baseStart_4615068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615107 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 3]
def baseStart_4615107 : Nat := 118140960795 + 4615107 * 2 ^ 59
def prefixEnd_4615107 : Nat := 4983230072969 + 3 ^ 40 * 4615107 * 2
def baseEnd_4615107 : Nat := 2369768162929580106338015

theorem tailTrace_4615107 : CollatzResearch.WordTrace tailWord_4615107 prefixEnd_4615107 2369768162929580106338015 := by
  unfold tailWord_4615107
  simp only [CollatzResearch.WordTrace]
  refine ⟨168326780891263011369099575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112217853927508674246066383 168326780891263011369099575)
  ·
    refine ⟨252490171336894517053649363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168326780891263011369099575 252490171336894517053649363)
    ·
      refine ⟨378735257005341775580474045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252490171336894517053649363 378735257005341775580474045)
      ·
        refine ⟨142025721377003165842677767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 378735257005341775580474045 142025721377003165842677767)
        ·
          refine ⟨213038582065504748764016651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142025721377003165842677767 213038582065504748764016651)
          ·
            refine ⟨319557873098257123146024977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213038582065504748764016651 319557873098257123146024977)
            ·
              refine ⟨239668404823692842359518733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319557873098257123146024977 239668404823692842359518733)
              ·
                refine ⟨89875651808884815884819525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239668404823692842359518733 89875651808884815884819525)
                ·
                  refine ⟨16851684714165902978403661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89875651808884815884819525 16851684714165902978403661)
                  ·
                    refine ⟨6319381767812213616901373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16851684714165902978403661 6319381767812213616901373)
                    ·
                      refine ⟨2369768162929580106338015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6319381767812213616901373 2369768162929580106338015)
                      ·
                        rfl

theorem cell23_4615107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_4615107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615107 prefixEnd_4615107 := by exact prefixLift 4615107
  have htrace : WordTrace (prefixWord ++ tailWord_4615107) baseStart_4615107 baseEnd_4615107 := by
    simpa [prefixWord, tailWord_4615107, baseEnd_4615107] using wordTrace_append hprefix tailTrace_4615107
  have hstable : (prefixWord ++ tailWord_4615107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615107).length < 2 ^ (prefixWord ++ tailWord_4615107).sum := by decide
  have hdescent : baseEnd_4615107 < baseStart_4615107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615124 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_4615124 : Nat := 118140960795 + 4615124 * 2 ^ 59
def prefixEnd_4615124 : Nat := 4983230072969 + 3 ^ 40 * 4615124 * 2
def baseEnd_4615124 : Nat := 2369776892100706539825437

theorem tailTrace_4615124 : CollatzResearch.WordTrace tailWord_4615124 prefixEnd_4615124 2369776892100706539825437 := by
  unfold tailWord_4615124
  simp only [CollatzResearch.WordTrace]
  refine ⟨84163700466100711636234213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112218267288134282181645617 84163700466100711636234213)
  ·
    refine ⟨15780693837393883431793915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84163700466100711636234213 15780693837393883431793915)
    ·
      refine ⟨23671040756090825147690873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15780693837393883431793915 23671040756090825147690873)
      ·
        refine ⟨17753280567068118860768155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23671040756090825147690873 17753280567068118860768155)
        ·
          refine ⟨26629920850602178291152233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17753280567068118860768155 26629920850602178291152233)
          ·
            refine ⟨19972440637951633718364175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26629920850602178291152233 19972440637951633718364175)
            ·
              refine ⟨29958660956927450577546263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19972440637951633718364175 29958660956927450577546263)
              ·
                refine ⟨44937991435391175866319395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29958660956927450577546263 44937991435391175866319395)
                ·
                  refine ⟨67406987153086763799479093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44937991435391175866319395 67406987153086763799479093)
                  ·
                    refine ⟨6319405045601884106201165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67406987153086763799479093 6319405045601884106201165)
                    ·
                      refine ⟨2369776892100706539825437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6319405045601884106201165 2369776892100706539825437)
                      ·
                        rfl

theorem cell23_4615124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_4615124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615124 prefixEnd_4615124 := by exact prefixLift 4615124
  have htrace : WordTrace (prefixWord ++ tailWord_4615124) baseStart_4615124 baseEnd_4615124 := by
    simpa [prefixWord, tailWord_4615124, baseEnd_4615124] using wordTrace_append hprefix tailTrace_4615124
  have hstable : (prefixWord ++ tailWord_4615124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615124).length < 2 ^ (prefixWord ++ tailWord_4615124).sum := by decide
  have hdescent : baseEnd_4615124 < baseStart_4615124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615144 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 2, 5]
def baseStart_4615144 : Nat := 118140960795 + 4615144 * 2 ^ 59
def prefixEnd_4615144 : Nat := 4983230072969 + 3 ^ 40 * 4615144 * 2
def baseEnd_4615144 : Nat := 789929053904598820525115

theorem tailTrace_4615144 : CollatzResearch.WordTrace tailWord_4615144 prefixEnd_4615144 789929053904598820525115 := by
  unfold tailWord_4615144
  simp only [CollatzResearch.WordTrace]
  refine ⟨84164065196064483344098243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112218753594752644458797657 84164065196064483344098243)
  ·
    refine ⟨126246097794096725016147365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84164065196064483344098243 126246097794096725016147365)
    ·
      refine ⟨23671143336393135940527631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126246097794096725016147365 23671143336393135940527631)
      ·
        refine ⟨35506715004589703910791447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23671143336393135940527631 35506715004589703910791447)
        ·
          refine ⟨53260072506884555866187171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35506715004589703910791447 53260072506884555866187171)
          ·
            refine ⟨79890108760326833799280757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53260072506884555866187171 79890108760326833799280757)
            ·
              refine ⟨7489697696280640668682571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79890108760326833799280757 7489697696280640668682571)
              ·
                refine ⟨11234546544420961003023857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7489697696280640668682571 11234546544420961003023857)
                ·
                  refine ⟨8425909908315720752267893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11234546544420961003023857 8425909908315720752267893)
                  ·
                    refine ⟨789929053904598820525115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8425909908315720752267893 789929053904598820525115)
                    ·
                      rfl

theorem cell23_4615144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_4615144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615144 prefixEnd_4615144 := by exact prefixLift 4615144
  have htrace : WordTrace (prefixWord ++ tailWord_4615144) baseStart_4615144 baseEnd_4615144 := by
    simpa [prefixWord, tailWord_4615144, baseEnd_4615144] using wordTrace_append hprefix tailTrace_4615144
  have hstable : (prefixWord ++ tailWord_4615144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615144).length < 2 ^ (prefixWord ++ tailWord_4615144).sum := by decide
  have hdescent : baseEnd_4615144 < baseStart_4615144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615191 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 3, 4]
def baseStart_4615191 : Nat := 118140960795 + 4615191 * 2 ^ 59
def prefixEnd_4615191 : Nat := 4983230072969 + 3 ^ 40 * 4615191 * 2
def baseEnd_4615191 : Nat := 789937098434852592562543

theorem tailTrace_4615191 : CollatzResearch.WordTrace tailWord_4615191 prefixEnd_4615191 789937098434852592562543 := by
  unfold tailWord_4615191
  simp only [CollatzResearch.WordTrace]
  refine ⟨168329844622958693715157427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112219896415305795810104951 168329844622958693715157427)
  ·
    refine ⟨252494766934438040572736141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168329844622958693715157427 252494766934438040572736141)
    ·
      refine ⟨94685537600414265214776053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252494766934438040572736141 94685537600414265214776053)
      ·
        refine ⟨8876769150038837363885255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94685537600414265214776053 8876769150038837363885255)
        ·
          refine ⟨13315153725058256045827883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8876769150038837363885255 13315153725058256045827883)
          ·
            refine ⟨19972730587587384068741825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13315153725058256045827883 19972730587587384068741825)
            ·
              refine ⟨14979547940690538051556369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19972730587587384068741825 14979547940690538051556369)
              ·
                refine ⟨11234660955517903538667277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14979547940690538051556369 11234660955517903538667277)
                ·
                  refine ⟨4212997858319213827000229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11234660955517903538667277 4212997858319213827000229)
                  ·
                    refine ⟨789937098434852592562543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4212997858319213827000229 789937098434852592562543)
                    ·
                      rfl

theorem cell23_4615191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_4615191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615191 prefixEnd_4615191 := by exact prefixLift 4615191
  have htrace : WordTrace (prefixWord ++ tailWord_4615191) baseStart_4615191 baseEnd_4615191 := by
    simpa [prefixWord, tailWord_4615191, baseEnd_4615191] using wordTrace_append hprefix tailTrace_4615191
  have hstable : (prefixWord ++ tailWord_4615191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615191).length < 2 ^ (prefixWord ++ tailWord_4615191).sum := by decide
  have hdescent : baseEnd_4615191 < baseStart_4615191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615204 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 8]
def baseStart_4615204 : Nat := 118140960795 + 4615204 * 2 ^ 59
def prefixEnd_4615204 : Nat := 4983230072969 + 3 ^ 40 * 4615204 * 2
def baseEnd_4615204 : Nat := 263313107839229580758341

theorem tailTrace_4615204 : CollatzResearch.WordTrace tailWord_4615204 prefixEnd_4615204 263313107839229580758341 := by
  unfold tailWord_4615204
  simp only [CollatzResearch.WordTrace]
  refine ⟨84165159385955798467690333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112220212514607731290253777 84165159385955798467690333)
  ·
    refine ⟨31561934769733424425383875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84165159385955798467690333 31561934769733424425383875)
    ·
      refine ⟨47342902154600136638075813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31561934769733424425383875 47342902154600136638075813)
      ·
        refine ⟨8876794153987525619639215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47342902154600136638075813 8876794153987525619639215)
        ·
          refine ⟨13315191230981288429458823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8876794153987525619639215 13315191230981288429458823)
          ·
            refine ⟨19972786846471932644188235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13315191230981288429458823 19972786846471932644188235)
            ·
              refine ⟨29959180269707898966282353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19972786846471932644188235 29959180269707898966282353)
              ·
                refine ⟨22469385202280924224711765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29959180269707898966282353 22469385202280924224711765)
                ·
                  refine ⟨263313107839229580758341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22469385202280924224711765 263313107839229580758341)
                  ·
                    rfl

theorem cell23_4615204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_4615204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615204 prefixEnd_4615204 := by exact prefixLift 4615204
  have htrace : WordTrace (prefixWord ++ tailWord_4615204) baseStart_4615204 baseEnd_4615204 := by
    simpa [prefixWord, tailWord_4615204, baseEnd_4615204] using wordTrace_append hprefix tailTrace_4615204
  have hstable : (prefixWord ++ tailWord_4615204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615204).length < 2 ^ (prefixWord ++ tailWord_4615204).sum := by decide
  have hdescent : baseEnd_4615204 < baseStart_4615204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615225 : List Nat := [1, 2, 1, 5, 2, 2, 3, 2, 1, 4]
def baseStart_4615225 : Nat := 118140960795 + 4615225 * 2 ^ 59
def prefixEnd_4615225 : Nat := 4983230072969 + 3 ^ 40 * 4615225 * 2
def baseEnd_4615225 : Nat := 789942917882270214887491

theorem tailTrace_4615225 : CollatzResearch.WordTrace tailWord_4615225 prefixEnd_4615225 789942917882270214887491 := by
  unfold tailWord_4615225
  simp only [CollatzResearch.WordTrace]
  refine ⟨168331084704835517521895129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112220723136557011681263419 168331084704835517521895129)
  ·
    refine ⟨126248313528626638141421347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168331084704835517521895129 126248313528626638141421347)
    ·
      refine ⟨189372470292939957212132021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126248313528626638141421347 189372470292939957212132021)
      ·
        refine ⟨17753669089963120988637377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189372470292939957212132021 17753669089963120988637377)
        ·
          refine ⟨13315251817472340741478033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17753669089963120988637377 13315251817472340741478033)
          ·
            refine ⟨9986438863104255556108525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13315251817472340741478033 9986438863104255556108525)
            ·
              refine ⟨3744914573664095833540697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9986438863104255556108525 3744914573664095833540697)
              ·
                refine ⟨2808685930248071875155523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744914573664095833540697 2808685930248071875155523)
                ·
                  refine ⟨4213028895372107812733285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808685930248071875155523 4213028895372107812733285)
                  ·
                    refine ⟨789942917882270214887491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4213028895372107812733285 789942917882270214887491)
                    ·
                      rfl

theorem cell23_4615225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 1, 4].length) (baseStart_4615225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615225 prefixEnd_4615225 := by exact prefixLift 4615225
  have htrace : WordTrace (prefixWord ++ tailWord_4615225) baseStart_4615225 baseEnd_4615225 := by
    simpa [prefixWord, tailWord_4615225, baseEnd_4615225] using wordTrace_append hprefix tailTrace_4615225
  have hstable : (prefixWord ++ tailWord_4615225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615225).length < 2 ^ (prefixWord ++ tailWord_4615225).sum := by decide
  have hdescent : baseEnd_4615225 < baseStart_4615225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615238 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_4615238 : Nat := 118140960795 + 4615238 * 2 ^ 59
def prefixEnd_4615238 : Nat := 4983230072969 + 3 ^ 40 * 4615238 * 2
def baseEnd_4615238 : Nat := 263315047655035454866657

theorem tailTrace_4615238 : CollatzResearch.WordTrace tailWord_4615238 prefixEnd_4615238 263315047655035454866657 := by
  unfold tailWord_4615238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5260361214180888148191199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 112221039235858947161412245 5260361214180888148191199)
  ·
    refine ⟨7890541821271332222286799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5260361214180888148191199 7890541821271332222286799)
    ·
      refine ⟨11835812731906998333430199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7890541821271332222286799 11835812731906998333430199)
      ·
        refine ⟨17753719097860497500145299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11835812731906998333430199 17753719097860497500145299)
        ·
          refine ⟨26630578646790746250217949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17753719097860497500145299 26630578646790746250217949)
          ·
            refine ⟨9986466992546529843831731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26630578646790746250217949 9986466992546529843831731)
            ·
              refine ⟨14979700488819794765747597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9986466992546529843831731 14979700488819794765747597)
              ·
                refine ⟨5617387683307423037155349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14979700488819794765747597 5617387683307423037155349)
                ·
                  refine ⟨263315047655035454866657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5617387683307423037155349 263315047655035454866657)
                  ·
                    rfl

theorem cell23_4615238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_4615238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615238 prefixEnd_4615238 := by exact prefixLift 4615238
  have htrace : WordTrace (prefixWord ++ tailWord_4615238) baseStart_4615238 baseEnd_4615238 := by
    simpa [prefixWord, tailWord_4615238, baseEnd_4615238] using wordTrace_append hprefix tailTrace_4615238
  have hstable : (prefixWord ++ tailWord_4615238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615238).length < 2 ^ (prefixWord ++ tailWord_4615238).sum := by decide
  have hdescent : baseEnd_4615238 < baseStart_4615238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615264 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 1, 6]
def baseStart_4615264 : Nat := 118140960795 + 4615264 * 2 ^ 59
def prefixEnd_4615264 : Nat := 4983230072969 + 3 ^ 40 * 4615264 * 2
def baseEnd_4615264 : Nat := 789949593130778664024931

theorem tailTrace_4615264 : CollatzResearch.WordTrace tailWord_4615264 prefixEnd_4615264 789949593130778664024931 := by
  unfold tailWord_4615264
  simp only [CollatzResearch.WordTrace]
  refine ⟨84166253575847113591282423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112221671434462818121709897 84166253575847113591282423)
  ·
    refine ⟨126249380363770670386923635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84166253575847113591282423 126249380363770670386923635)
    ·
      refine ⟨189374070545656005580385453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126249380363770670386923635 189374070545656005580385453)
      ·
        refine ⟨71015276454621002092644545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189374070545656005580385453 71015276454621002092644545)
        ·
          refine ⟨53261457340965751569483409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71015276454621002092644545 53261457340965751569483409)
          ·
            refine ⟨39946093005724313677112557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53261457340965751569483409 39946093005724313677112557)
            ·
              refine ⟨14979784877146617628917209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39946093005724313677112557 14979784877146617628917209)
              ·
                refine ⟨11234838657859963221687907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14979784877146617628917209 11234838657859963221687907)
                ·
                  refine ⟨16852257986789944832531861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11234838657859963221687907 16852257986789944832531861)
                  ·
                    refine ⟨789949593130778664024931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16852257986789944832531861 789949593130778664024931)
                    ·
                      rfl

theorem cell23_4615264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_4615264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615264 prefixEnd_4615264 := by exact prefixLift 4615264
  have htrace : WordTrace (prefixWord ++ tailWord_4615264) baseStart_4615264 baseEnd_4615264 := by
    simpa [prefixWord, tailWord_4615264, baseEnd_4615264] using wordTrace_append hprefix tailTrace_4615264
  have hstable : (prefixWord ++ tailWord_4615264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615264).length < 2 ^ (prefixWord ++ tailWord_4615264).sum := by decide
  have hdescent : baseEnd_4615264 < baseStart_4615264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615322 : List Nat := [3, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4615322 : Nat := 118140960795 + 4615322 * 2 ^ 59
def prefixEnd_4615322 : Nat := 4983230072969 + 3 ^ 40 * 4615322 * 2
def baseEnd_4615322 : Nat := 2369878561270296765149527

theorem tailTrace_4615322 : CollatzResearch.WordTrace tailWord_4615322 prefixEnd_4615322 2369878561270296765149527 := by
  unfold tailWord_4615322
  simp only [CollatzResearch.WordTrace]
  refine ⟨42083655646371025772044055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112223081723656068725450813 42083655646371025772044055)
  ·
    refine ⟨63125483469556538658066083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42083655646371025772044055 63125483469556538658066083)
    ·
      refine ⟨94688225204334807987099125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63125483469556538658066083 94688225204334807987099125)
      ·
        refine ⟨8877021112906388248790543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94688225204334807987099125 8877021112906388248790543)
        ·
          refine ⟨13315531669359582373185815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8877021112906388248790543 13315531669359582373185815)
          ·
            refine ⟨19973297504039373559778723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13315531669359582373185815 19973297504039373559778723)
            ·
              refine ⟨29959946256059060339668085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19973297504039373559778723 29959946256059060339668085)
              ·
                refine ⟨2808744961505536906843883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29959946256059060339668085 2808744961505536906843883)
                ·
                  refine ⟨4213117442258305360265825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808744961505536906843883 4213117442258305360265825)
                  ·
                    refine ⟨3159838081693729020199369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4213117442258305360265825 3159838081693729020199369)
                    ·
                      refine ⟨2369878561270296765149527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159838081693729020199369 2369878561270296765149527)
                      ·
                        rfl

theorem cell23_4615322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4615322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615322 prefixEnd_4615322 := by exact prefixLift 4615322
  have htrace : WordTrace (prefixWord ++ tailWord_4615322) baseStart_4615322 baseEnd_4615322 := by
    simpa [prefixWord, tailWord_4615322, baseEnd_4615322] using wordTrace_append hprefix tailTrace_4615322
  have hstable : (prefixWord ++ tailWord_4615322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615322).length < 2 ^ (prefixWord ++ tailWord_4615322).sum := by decide
  have hdescent : baseEnd_4615322 < baseStart_4615322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615362 : List Nat := [3, 5, 1, 1, 2, 2, 2, 7]
def baseStart_4615362 : Nat := 118140960795 + 4615362 * 2 ^ 59
def prefixEnd_4615362 : Nat := 4983230072969 + 3 ^ 40 * 4615362 * 2
def baseEnd_4615362 : Nat := 87774040759128763283309

theorem tailTrace_4615362 : CollatzResearch.WordTrace tailWord_4615362 prefixEnd_4615362 87774040759128763283309 := by
  unfold tailWord_4615362
  simp only [CollatzResearch.WordTrace]
  refine ⟨42084020376334797479908085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112224054336892793279754893 42084020376334797479908085)
  ·
    refine ⟨3945376910281387263741383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42084020376334797479908085 3945376910281387263741383)
    ·
      refine ⟨5918065365422080895612075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3945376910281387263741383 5918065365422080895612075)
      ·
        refine ⟨8877098048133121343418113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5918065365422080895612075 8877098048133121343418113)
        ·
          refine ⟨6657823536099841007563585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8877098048133121343418113 6657823536099841007563585)
          ·
            refine ⟨4993367652074880755672689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6657823536099841007563585 4993367652074880755672689)
            ·
              refine ⟨3745025739056160566754517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4993367652074880755672689 3745025739056160566754517)
              ·
                refine ⟨87774040759128763283309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3745025739056160566754517 87774040759128763283309)
                ·
                  rfl

theorem cell23_4615362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 7].length) (baseStart_4615362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615362 prefixEnd_4615362 := by exact prefixLift 4615362
  have htrace : WordTrace (prefixWord ++ tailWord_4615362) baseStart_4615362 baseEnd_4615362 := by
    simpa [prefixWord, tailWord_4615362, baseEnd_4615362] using wordTrace_append hprefix tailTrace_4615362
  have hstable : (prefixWord ++ tailWord_4615362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615362).length < 2 ^ (prefixWord ++ tailWord_4615362).sum := by decide
  have hdescent : baseEnd_4615362 < baseStart_4615362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615373 : List Nat := [1, 6, 2, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4615373 : Nat := 118140960795 + 4615373 * 2 ^ 59
def prefixEnd_4615373 : Nat := 4983230072969 + 3 ^ 40 * 4615373 * 2
def baseEnd_4615373 : Nat := 2369904748783676065611793

theorem tailTrace_4615373 : CollatzResearch.WordTrace tailWord_4615373 prefixEnd_4615373 2369904748783676065611793 := by
  unfold tailWord_4615373
  simp only [CollatzResearch.WordTrace]
  refine ⟨168336482708299338798282773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112224321805532892532188515 168336482708299338798282773)
  ·
    refine ⟨7890772626951531506169505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 168336482708299338798282773 7890772626951531506169505)
    ·
      refine ⟨5918079470213648629627129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7890772626951531506169505 5918079470213648629627129)
      ·
        refine ⟨4438559602660236472220347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5918079470213648629627129 4438559602660236472220347)
        ·
          refine ⟨6657839403990354708330521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4438559602660236472220347 6657839403990354708330521)
          ·
            refine ⟨4993379552992766031247891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6657839403990354708330521 4993379552992766031247891)
            ·
              refine ⟨7490069329489149046871837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4993379552992766031247891 7490069329489149046871837)
              ·
                refine ⟨2808775998558430892576939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7490069329489149046871837 2808775998558430892576939)
                ·
                  refine ⟨4213163997837646338865409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808775998558430892576939 4213163997837646338865409)
                  ·
                    refine ⟨3159872998378234754149057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4213163997837646338865409 3159872998378234754149057)
                    ·
                      refine ⟨2369904748783676065611793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159872998378234754149057 2369904748783676065611793)
                      ·
                        rfl

theorem cell23_4615373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4615373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615373 prefixEnd_4615373 := by exact prefixLift 4615373
  have htrace : WordTrace (prefixWord ++ tailWord_4615373) baseStart_4615373 baseEnd_4615373 := by
    simpa [prefixWord, tailWord_4615373, baseEnd_4615373] using wordTrace_append hprefix tailTrace_4615373
  have hstable : (prefixWord ++ tailWord_4615373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615373).length < 2 ^ (prefixWord ++ tailWord_4615373).sum := by decide
  have hdescent : baseEnd_4615373 < baseStart_4615373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615378 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_4615378 : Nat := 118140960795 + 4615378 * 2 ^ 59
def prefixEnd_4615378 : Nat := 4983230072969 + 3 ^ 40 * 4615378 * 2
def baseEnd_4615378 : Nat := 2369907316186948546049269

theorem tailTrace_4615378 : CollatzResearch.WordTrace tailWord_4615378 prefixEnd_4615378 2369907316186948546049269 := by
  unfold tailWord_4615378
  simp only [CollatzResearch.WordTrace]
  refine ⟨42084166268320306163053697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112224443382187483101476525 42084166268320306163053697)
  ·
    refine ⟨31563124701240229622290273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42084166268320306163053697 31563124701240229622290273)
    ·
      refine ⟨23672343525930172216717705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31563124701240229622290273 23672343525930172216717705)
      ·
        refine ⟨17754257644447629162538279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23672343525930172216717705 17754257644447629162538279)
        ·
          refine ⟨26631386466671443743807419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17754257644447629162538279 26631386466671443743807419)
          ·
            refine ⟨39947079700007165615711129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26631386466671443743807419 39947079700007165615711129)
            ·
              refine ⟨29960309775005374211783347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39947079700007165615711129 29960309775005374211783347)
              ·
                refine ⟨44940464662508061317675021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29960309775005374211783347 44940464662508061317675021)
                ·
                  refine ⟨16852674248440522994128133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44940464662508061317675021 16852674248440522994128133)
                  ·
                    refine ⟨3159876421582598061399025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16852674248440522994128133 3159876421582598061399025)
                    ·
                      refine ⟨2369907316186948546049269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3159876421582598061399025 2369907316186948546049269)
                      ·
                        rfl

theorem cell23_4615378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_4615378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615378 prefixEnd_4615378 := by exact prefixLift 4615378
  have htrace : WordTrace (prefixWord ++ tailWord_4615378) baseStart_4615378 baseEnd_4615378 := by
    simpa [prefixWord, tailWord_4615378, baseEnd_4615378] using wordTrace_append hprefix tailTrace_4615378
  have hstable : (prefixWord ++ tailWord_4615378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615378).length < 2 ^ (prefixWord ++ tailWord_4615378).sum := by decide
  have hdescent : baseEnd_4615378 < baseStart_4615378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615381 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4615381 : Nat := 118140960795 + 4615381 * 2 ^ 59
def prefixEnd_4615381 : Nat := 4983230072969 + 3 ^ 40 * 4615381 * 2
def baseEnd_4615381 : Nat := 2369908856628912034311755

theorem tailTrace_4615381 : CollatzResearch.WordTrace tailWord_4615381 prefixEnd_4615381 2369908856628912034311755 := by
  unfold tailWord_4615381
  simp only [CollatzResearch.WordTrace]
  refine ⟨168336774492270356164573997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112224516328180237443049331 168336774492270356164573997)
  ·
    refine ⟨63126290434601383561715249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168336774492270356164573997 63126290434601383561715249)
    ·
      refine ⟨47344717825951037671286437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63126290434601383561715249 47344717825951037671286437)
      ·
        refine ⟨8877134592365819563366207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47344717825951037671286437 8877134592365819563366207)
        ·
          refine ⟨13315701888548729345049311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8877134592365819563366207 13315701888548729345049311)
          ·
            refine ⟨19973552832823094017573967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13315701888548729345049311 19973552832823094017573967)
            ·
              refine ⟨29960329249234641026360951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19973552832823094017573967 29960329249234641026360951)
              ·
                refine ⟨44940493873851961539541427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29960329249234641026360951 44940493873851961539541427)
                ·
                  refine ⟨67410740810777942309312141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44940493873851961539541427 67410740810777942309312141)
                  ·
                    refine ⟨25279027804041728365992053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67410740810777942309312141 25279027804041728365992053)
                    ·
                      refine ⟨2369908856628912034311755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25279027804041728365992053 2369908856628912034311755)
                      ·
                        rfl

theorem cell23_4615381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4615381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615381 prefixEnd_4615381 := by exact prefixLift 4615381
  have htrace : WordTrace (prefixWord ++ tailWord_4615381) baseStart_4615381 baseEnd_4615381 := by
    simpa [prefixWord, tailWord_4615381, baseEnd_4615381] using wordTrace_append hprefix tailTrace_4615381
  have hstable : (prefixWord ++ tailWord_4615381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615381).length < 2 ^ (prefixWord ++ tailWord_4615381).sum := by decide
  have hdescent : baseEnd_4615381 < baseStart_4615381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615424 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_4615424 : Nat := 118140960795 + 4615424 * 2 ^ 59
def prefixEnd_4615424 : Nat := 4983230072969 + 3 ^ 40 * 4615424 * 2
def baseEnd_4615424 : Nat := 2369930936297055366074057

theorem tailTrace_4615424 : CollatzResearch.WordTrace tailWord_4615424 prefixEnd_4615424 2369930936297055366074057 := by
  unfold tailWord_4615424
  simp only [CollatzResearch.WordTrace]
  refine ⟨84169171415557287254194663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112225561887409716338926217 84169171415557287254194663)
  ·
    refine ⟨126253757123335930881291995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84169171415557287254194663 126253757123335930881291995)
    ·
      refine ⟨189380635685003896321937993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126253757123335930881291995 189380635685003896321937993)
      ·
        refine ⟨142035476763752922241453495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189380635685003896321937993 142035476763752922241453495)
        ·
          refine ⟨213053215145629383362180243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142035476763752922241453495 213053215145629383362180243)
          ·
            refine ⟨319579822718444075043270365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213053215145629383362180243 319579822718444075043270365)
            ·
              refine ⟨119842433519416528141226387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 319579822718444075043270365 119842433519416528141226387)
              ·
                refine ⟨179763650279124792211839581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119842433519416528141226387 179763650279124792211839581)
                ·
                  refine ⟨67411368854671797079439843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179763650279124792211839581 67411368854671797079439843)
                  ·
                    refine ⟨101117053282007695619159765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67411368854671797079439843 101117053282007695619159765)
                    ·
                      refine ⟨2369930936297055366074057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101117053282007695619159765 2369930936297055366074057)
                      ·
                        rfl

theorem cell23_4615424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_4615424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615424 prefixEnd_4615424 := by exact prefixLift 4615424
  have htrace : WordTrace (prefixWord ++ tailWord_4615424) baseStart_4615424 baseEnd_4615424 := by
    simpa [prefixWord, tailWord_4615424, baseEnd_4615424] using wordTrace_append hprefix tailTrace_4615424
  have hstable : (prefixWord ++ tailWord_4615424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615424).length < 2 ^ (prefixWord ++ tailWord_4615424).sum := by decide
  have hdescent : baseEnd_4615424 < baseStart_4615424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615471 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 3]
def baseStart_4615471 : Nat := 118140960795 + 4615471 * 2 ^ 59
def prefixEnd_4615471 : Nat := 4983230072969 + 3 ^ 40 * 4615471 * 2
def baseEnd_4615471 : Nat := 2369955069887816682186341

theorem tailTrace_4615471 : CollatzResearch.WordTrace tailWord_4615471 prefixEnd_4615471 2369955069887816682186341 := by
  unfold tailWord_4615471
  simp only [CollatzResearch.WordTrace]
  refine ⟨168340057061944301535350267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112226704707962867690233511 168340057061944301535350267)
  ·
    refine ⟨252510085592916452303025401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168340057061944301535350267 252510085592916452303025401)
    ·
      refine ⟨189382564194687339227269051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252510085592916452303025401 189382564194687339227269051)
      ·
        refine ⟨284073846292031008840903577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189382564194687339227269051 284073846292031008840903577)
        ·
          refine ⟨213055384719023256630677683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284073846292031008840903577 213055384719023256630677683)
          ·
            refine ⟨319583077078534884946016525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213055384719023256630677683 319583077078534884946016525)
            ·
              refine ⟨119843653904450581854756197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 319583077078534884946016525 119843653904450581854756197)
              ·
                refine ⟨22470685107084484097766787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119843653904450581854756197 22470685107084484097766787)
                ·
                  refine ⟨33706027660626726146650181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22470685107084484097766787 33706027660626726146650181)
                  ·
                    refine ⟨6319880186367511152496909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33706027660626726146650181 6319880186367511152496909)
                    ·
                      refine ⟨2369955069887816682186341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6319880186367511152496909 2369955069887816682186341)
                      ·
                        rfl

theorem cell23_4615471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 3].length) (baseStart_4615471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615471 prefixEnd_4615471 := by exact prefixLift 4615471
  have htrace : WordTrace (prefixWord ++ tailWord_4615471) baseStart_4615471 baseEnd_4615471 := by
    simpa [prefixWord, tailWord_4615471, baseEnd_4615471] using wordTrace_append hprefix tailTrace_4615471
  have hstable : (prefixWord ++ tailWord_4615471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615471).length < 2 ^ (prefixWord ++ tailWord_4615471).sum := by decide
  have hdescent : baseEnd_4615471 < baseStart_4615471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615485 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4615485 : Nat := 118140960795 + 4615485 * 2 ^ 59
def prefixEnd_4615485 : Nat := 4983230072969 + 3 ^ 40 * 4615485 * 2
def baseEnd_4615485 : Nat := 2369962258616979627411277

theorem tailTrace_4615485 : CollatzResearch.WordTrace tailWord_4615485 prefixEnd_4615485 2369962258616979627411277 := by
  unfold tailWord_4615485
  simp only [CollatzResearch.WordTrace]
  refine ⟨168340567683893581926359909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112227045122595721284239939 168340567683893581926359909)
  ·
    refine ⟨31563856440730046611192483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168340567683893581926359909 31563856440730046611192483)
    ·
      refine ⟨47345784661095069916788725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31563856440730046611192483 47345784661095069916788725)
      ·
        refine ⟨4438667311977662804698943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47345784661095069916788725 4438667311977662804698943)
        ·
          refine ⟨6658000967966494207048415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4438667311977662804698943 6658000967966494207048415)
          ·
            refine ⟨9987001451949741310572623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6658000967966494207048415 9987001451949741310572623)
            ·
              refine ⟨14980502177924611965858935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9987001451949741310572623 14980502177924611965858935)
              ·
                refine ⟨22470753266886917948788403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14980502177924611965858935 22470753266886917948788403)
                ·
                  refine ⟨33706129900330376923182605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22470753266886917948788403 33706129900330376923182605)
                  ·
                    refine ⟨12639798712623891346193477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33706129900330376923182605 12639798712623891346193477)
                    ·
                      refine ⟨2369962258616979627411277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12639798712623891346193477 2369962258616979627411277)
                      ·
                        rfl

theorem cell23_4615485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4615485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615485 prefixEnd_4615485 := by exact prefixLift 4615485
  have htrace : WordTrace (prefixWord ++ tailWord_4615485) baseStart_4615485 baseEnd_4615485 := by
    simpa [prefixWord, tailWord_4615485, baseEnd_4615485] using wordTrace_append hprefix tailTrace_4615485
  have hstable : (prefixWord ++ tailWord_4615485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615485).length < 2 ^ (prefixWord ++ tailWord_4615485).sum := by decide
  have hdescent : baseEnd_4615485 < baseStart_4615485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615495 : List Nat := [1, 1, 4, 1, 2, 3, 1, 5, 1, 4]
def baseStart_4615495 : Nat := 118140960795 + 4615495 * 2 ^ 59
def prefixEnd_4615495 : Nat := 4983230072969 + 3 ^ 40 * 4615495 * 2
def baseEnd_4615495 : Nat := 789989131141174862762077

theorem tailTrace_4615495 : CollatzResearch.WordTrace tailWord_4615495 prefixEnd_4615495 789989131141174862762077 := by
  unfold tailWord_4615495
  simp only [CollatzResearch.WordTrace]
  refine ⟨168340932413857353634223939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112227288275904902422815959 168340932413857353634223939)
  ·
    refine ⟨252511398620786030451335909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168340932413857353634223939 252511398620786030451335909)
    ·
      refine ⟨47345887241397380709625483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252511398620786030451335909 47345887241397380709625483)
      ·
        refine ⟨71018830862096071064438225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47345887241397380709625483 71018830862096071064438225)
        ·
          refine ⟨53264123146572053298328669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71018830862096071064438225 53264123146572053298328669)
          ·
            refine ⟨19974046179964519986873251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53264123146572053298328669 19974046179964519986873251)
            ·
              refine ⟨29961069269946779980309877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19974046179964519986873251 29961069269946779980309877)
              ·
                refine ⟨2808850244057510623154051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29961069269946779980309877 2808850244057510623154051)
                ·
                  refine ⟨4213275366086265934731077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808850244057510623154051 4213275366086265934731077)
                  ·
                    refine ⟨789989131141174862762077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4213275366086265934731077 789989131141174862762077)
                    ·
                      rfl

theorem cell23_4615495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_4615495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615495 prefixEnd_4615495 := by exact prefixLift 4615495
  have htrace : WordTrace (prefixWord ++ tailWord_4615495) baseStart_4615495 baseEnd_4615495 := by
    simpa [prefixWord, tailWord_4615495, baseEnd_4615495] using wordTrace_append hprefix tailTrace_4615495
  have hstable : (prefixWord ++ tailWord_4615495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615495).length < 2 ^ (prefixWord ++ tailWord_4615495).sum := by decide
  have hdescent : baseEnd_4615495 < baseStart_4615495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615511 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_4615511 : Nat := 118140960795 + 4615511 * 2 ^ 59
def prefixEnd_4615511 : Nat := 4983230072969 + 3 ^ 40 * 4615511 * 2
def baseEnd_4615511 : Nat := 2369975609113996525686157

theorem tailTrace_4615511 : CollatzResearch.WordTrace tailWord_4615511 prefixEnd_4615511 2369975609113996525686157 := by
  unfold tailWord_4615511
  simp only [CollatzResearch.WordTrace]
  refine ⟨168341515981799388366806387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112227677321199592244537591 168341515981799388366806387)
  ·
    refine ⟨252512273972699082550209581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168341515981799388366806387 252512273972699082550209581)
    ·
      refine ⟨94692102739762155956328593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252512273972699082550209581 94692102739762155956328593)
      ·
        refine ⟨71019077054821616967246445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94692102739762155956328593 71019077054821616967246445)
        ·
          refine ⟨26632153895558106362717417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71019077054821616967246445 26632153895558106362717417)
          ·
            refine ⟨19974115421668579772038063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26632153895558106362717417 19974115421668579772038063)
            ·
              refine ⟨29961173132502869658057095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19974115421668579772038063 29961173132502869658057095)
              ·
                refine ⟨44941759698754304487085643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29961173132502869658057095 44941759698754304487085643)
                ·
                  refine ⟨67412639548131456730628465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44941759698754304487085643 67412639548131456730628465)
                  ·
                    refine ⟨50559479661098592547971349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67412639548131456730628465 50559479661098592547971349)
                    ·
                      refine ⟨2369975609113996525686157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50559479661098592547971349 2369975609113996525686157)
                      ·
                        rfl

theorem cell23_4615511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_4615511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615511 prefixEnd_4615511 := by exact prefixLift 4615511
  have htrace : WordTrace (prefixWord ++ tailWord_4615511) baseStart_4615511 baseEnd_4615511 := by
    simpa [prefixWord, tailWord_4615511, baseEnd_4615511] using wordTrace_append hprefix tailTrace_4615511
  have hstable : (prefixWord ++ tailWord_4615511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615511).length < 2 ^ (prefixWord ++ tailWord_4615511).sum := by decide
  have hdescent : baseEnd_4615511 < baseStart_4615511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615521 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 5, 5]
def baseStart_4615521 : Nat := 118140960795 + 4615521 * 2 ^ 59
def prefixEnd_4615521 : Nat := 4983230072969 + 3 ^ 40 * 4615521 * 2
def baseEnd_4615521 : Nat := 789993581306847162187037

theorem tailTrace_4615521 : CollatzResearch.WordTrace tailWord_4615521 prefixEnd_4615521 789993581306847162187037 := by
  unfold tailWord_4615521
  simp only [CollatzResearch.WordTrace]
  refine ⟨168341880711763160074670417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112227920474508773383113611 168341880711763160074670417)
  ·
    refine ⟨126256410533822370056002813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168341880711763160074670417 126256410533822370056002813)
    ·
      refine ⟨47346153950183388771001055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126256410533822370056002813 47346153950183388771001055)
      ·
        refine ⟨71019230925275083156501583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47346153950183388771001055 71019230925275083156501583)
        ·
          refine ⟨106528846387912624734752375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71019230925275083156501583 106528846387912624734752375)
          ·
            refine ⟨159793269581868937102128563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106528846387912624734752375 159793269581868937102128563)
            ·
              refine ⟨239689904372803405653192845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159793269581868937102128563 239689904372803405653192845)
              ·
                refine ⟨89883714139801277119947317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239689904372803405653192845 89883714139801277119947317)
                ·
                  refine ⟨8426598200606369729995061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89883714139801277119947317 8426598200606369729995061)
                  ·
                    refine ⟨789993581306847162187037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8426598200606369729995061 789993581306847162187037)
                    ·
                      rfl

theorem cell23_4615521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_4615521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615521 prefixEnd_4615521 := by exact prefixLift 4615521
  have htrace : WordTrace (prefixWord ++ tailWord_4615521) baseStart_4615521 baseEnd_4615521 := by
    simpa [prefixWord, tailWord_4615521, baseEnd_4615521] using wordTrace_append hprefix tailTrace_4615521
  have hstable : (prefixWord ++ tailWord_4615521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615521).length < 2 ^ (prefixWord ++ tailWord_4615521).sum := by decide
  have hdescent : baseEnd_4615521 < baseStart_4615521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615578 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4615578 : Nat := 118140960795 + 4615578 * 2 ^ 59
def prefixEnd_4615578 : Nat := 4983230072969 + 3 ^ 40 * 4615578 * 2
def baseEnd_4615578 : Nat := 2370010012317847763548349

theorem tailTrace_4615578 : CollatzResearch.WordTrace tailWord_4615578 prefixEnd_4615578 2370010012317847763548349 := by
  unfold tailWord_4615578
  simp only [CollatzResearch.WordTrace]
  refine ⟨42085989918139164702373847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112229306448371105872996925 42085989918139164702373847)
  ·
    refine ⟨63128984877208747053560771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42085989918139164702373847 63128984877208747053560771)
    ·
      refine ⟨94693477315813120580341157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63128984877208747053560771 94693477315813120580341157)
      ·
        refine ⟨17755026996714960108813967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94693477315813120580341157 17755026996714960108813967)
        ·
          refine ⟨26632540495072440163220951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17755026996714960108813967 26632540495072440163220951)
          ·
            refine ⟨39948810742608660244831427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26632540495072440163220951 39948810742608660244831427)
            ·
              refine ⟨59923216113912990367247141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39948810742608660244831427 59923216113912990367247141)
              ·
                refine ⟨11235603021358685693858839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59923216113912990367247141 11235603021358685693858839)
                ·
                  refine ⟨16853404532038028540788259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11235603021358685693858839 16853404532038028540788259)
                  ·
                    refine ⟨25280106798057042811182389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16853404532038028540788259 25280106798057042811182389)
                    ·
                      refine ⟨2370010012317847763548349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25280106798057042811182389 2370010012317847763548349)
                      ·
                        rfl

theorem cell23_4615578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4615578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615578 prefixEnd_4615578 := by exact prefixLift 4615578
  have htrace : WordTrace (prefixWord ++ tailWord_4615578) baseStart_4615578 baseEnd_4615578 := by
    simpa [prefixWord, tailWord_4615578, baseEnd_4615578] using wordTrace_append hprefix tailTrace_4615578
  have hstable : (prefixWord ++ tailWord_4615578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615578).length < 2 ^ (prefixWord ++ tailWord_4615578).sum := by decide
  have hdescent : baseEnd_4615578 < baseStart_4615578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615588 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_4615588 : Nat := 118140960795 + 4615588 * 2 ^ 59
def prefixEnd_4615588 : Nat := 4983230072969 + 3 ^ 40 * 4615588 * 2
def baseEnd_4615588 : Nat := 2370015147124392724423303

theorem tailTrace_4615588 : CollatzResearch.WordTrace tailWord_4615588 prefixEnd_4615588 2370015147124392724423303 := by
  unfold tailWord_4615588
  simp only [CollatzResearch.WordTrace]
  refine ⟨84172162201260215258679709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112229549601680287011572945 84172162201260215258679709)
  ·
    refine ⟨31564560825472580722004891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84172162201260215258679709 31564560825472580722004891)
    ·
      refine ⟨47346841238208871083007337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31564560825472580722004891 47346841238208871083007337)
      ·
        refine ⟨35510130928656653312255503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47346841238208871083007337 35510130928656653312255503)
        ·
          refine ⟨53265196392984979968383255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35510130928656653312255503 53265196392984979968383255)
          ·
            refine ⟨79897794589477469952574883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53265196392984979968383255 79897794589477469952574883)
            ·
              refine ⟨119846691884216204928862325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79897794589477469952574883 119846691884216204928862325)
              ·
                refine ⟨11235627364145269212080843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119846691884216204928862325 11235627364145269212080843)
                ·
                  refine ⟨16853441046217903818121265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11235627364145269212080843 16853441046217903818121265)
                  ·
                    refine ⟨12640080784663427863590949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16853441046217903818121265 12640080784663427863590949)
                    ·
                      refine ⟨2370015147124392724423303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12640080784663427863590949 2370015147124392724423303)
                      ·
                        rfl

theorem cell23_4615588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_4615588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615588 prefixEnd_4615588 := by exact prefixLift 4615588
  have htrace : WordTrace (prefixWord ++ tailWord_4615588) baseStart_4615588 baseEnd_4615588 := by
    simpa [prefixWord, tailWord_4615588, baseEnd_4615588] using wordTrace_append hprefix tailTrace_4615588
  have hstable : (prefixWord ++ tailWord_4615588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615588).length < 2 ^ (prefixWord ++ tailWord_4615588).sum := by decide
  have hdescent : baseEnd_4615588 < baseStart_4615588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615592 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4615592 : Nat := 118140960795 + 4615592 * 2 ^ 59
def prefixEnd_4615592 : Nat := 4983230072969 + 3 ^ 40 * 4615592 * 2
def baseEnd_4615592 : Nat := 2370017201047010708773285

theorem tailTrace_4615592 : CollatzResearch.WordTrace tailWord_4615592 prefixEnd_4615592 2370017201047010708773285 := by
  unfold tailWord_4615592
  simp only [CollatzResearch.WordTrace]
  refine ⟨84172235147252969600252515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112229646863003959467003353 84172235147252969600252515)
  ·
    refine ⟨126258352720879454400378773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84172235147252969600252515 126258352720879454400378773)
    ·
      refine ⟨5918360283791224425017755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 126258352720879454400378773 5918360283791224425017755)
      ·
        refine ⟨8877540425686836637526633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5918360283791224425017755 8877540425686836637526633)
        ·
          refine ⟨6658155319265127478144975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8877540425686836637526633 6658155319265127478144975)
          ·
            refine ⟨9987232978897691217217463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6658155319265127478144975 9987232978897691217217463)
            ·
              refine ⟨14980849468346536825826195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9987232978897691217217463 14980849468346536825826195)
              ·
                refine ⟨22471274202519805238739293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14980849468346536825826195 22471274202519805238739293)
                ·
                  refine ⟨8426727825944926964527235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22471274202519805238739293 8426727825944926964527235)
                  ·
                    refine ⟨12640091738917390446790853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8426727825944926964527235 12640091738917390446790853)
                    ·
                      refine ⟨2370017201047010708773285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12640091738917390446790853 2370017201047010708773285)
                      ·
                        rfl

theorem cell23_4615592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4615592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615592 prefixEnd_4615592 := by exact prefixLift 4615592
  have htrace : WordTrace (prefixWord ++ tailWord_4615592) baseStart_4615592 baseEnd_4615592 := by
    simpa [prefixWord, tailWord_4615592, baseEnd_4615592] using wordTrace_append hprefix tailTrace_4615592
  have hstable : (prefixWord ++ tailWord_4615592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615592).length < 2 ^ (prefixWord ++ tailWord_4615592).sum := by decide
  have hdescent : baseEnd_4615592 < baseStart_4615592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615605 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4615605 : Nat := 118140960795 + 4615605 * 2 ^ 59
def prefixEnd_4615605 : Nat := 4983230072969 + 3 ^ 40 * 4615605 * 2
def baseEnd_4615605 : Nat := 2370023876295519157910725

theorem tailTrace_4615605 : CollatzResearch.WordTrace tailWord_4615605 prefixEnd_4615605 2370023876295519157910725 := by
  unfold tailWord_4615605
  simp only [CollatzResearch.WordTrace]
  refine ⟨168344944443458842420728269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112229962962305894947152179 168344944443458842420728269)
  ·
    refine ⟨63129354166297065907773101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168344944443458842420728269 63129354166297065907773101)
    ·
      refine ⟨23673507812361399715414913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63129354166297065907773101 23673507812361399715414913)
      ·
        refine ⟨17755130859271049786561185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23673507812361399715414913 17755130859271049786561185)
        ·
          refine ⟨13316348144453287339920889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17755130859271049786561185 13316348144453287339920889)
          ·
            refine ⟨9987261108339965504940667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13316348144453287339920889 9987261108339965504940667)
            ·
              refine ⟨14980891662509948257411001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9987261108339965504940667 14980891662509948257411001)
              ·
                refine ⟨11235668746882461193058251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14980891662509948257411001 11235668746882461193058251)
                ·
                  refine ⟨16853503120323691789587377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11235668746882461193058251 16853503120323691789587377)
                  ·
                    refine ⟨12640127340242768842190533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16853503120323691789587377 12640127340242768842190533)
                    ·
                      refine ⟨2370023876295519157910725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12640127340242768842190533 2370023876295519157910725)
                      ·
                        rfl

theorem cell23_4615605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4615605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615605 prefixEnd_4615605 := by exact prefixLift 4615605
  have htrace : WordTrace (prefixWord ++ tailWord_4615605) baseStart_4615605 baseEnd_4615605 := by
    simpa [prefixWord, tailWord_4615605, baseEnd_4615605] using wordTrace_append hprefix tailTrace_4615605
  have hstable : (prefixWord ++ tailWord_4615605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615605).length < 2 ^ (prefixWord ++ tailWord_4615605).sum := by decide
  have hdescent : baseEnd_4615605 < baseStart_4615605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615608 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 3, 3, 3]
def baseStart_4615608 : Nat := 118140960795 + 4615608 * 2 ^ 59
def prefixEnd_4615608 : Nat := 4983230072969 + 3 ^ 40 * 4615608 * 2
def baseEnd_4615608 : Nat := 2370025416737482646173211

theorem tailTrace_4615608 : CollatzResearch.WordTrace tailWord_4615608 prefixEnd_4615608 2370025416737482646173211 := by
  unfold tailWord_4615608
  simp only [CollatzResearch.WordTrace]
  refine ⟨84172526931223986966543739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112230035908298649288724985 84172526931223986966543739)
  ·
    refine ⟨126258790396835980449815609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84172526931223986966543739 126258790396835980449815609)
    ·
      refine ⟨94694092797626985337361707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126258790396835980449815609 94694092797626985337361707)
      ·
        refine ⟨142041139196440478006042561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94694092797626985337361707 142041139196440478006042561)
        ·
          refine ⟨106530854397330358504531921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142041139196440478006042561 106530854397330358504531921)
          ·
            refine ⟨79898140797997768878398941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106530854397330358504531921 79898140797997768878398941)
            ·
              refine ⟨29961802799249163329399603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79898140797997768878398941 29961802799249163329399603)
              ·
                refine ⟨44942704198873744994099405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29961802799249163329399603 44942704198873744994099405)
                ·
                  refine ⟨16853514074577654372787277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44942704198873744994099405 16853514074577654372787277)
                  ·
                    refine ⟨6320067777966620389795229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16853514074577654372787277 6320067777966620389795229)
                    ·
                      refine ⟨2370025416737482646173211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6320067777966620389795229 2370025416737482646173211)
                      ·
                        rfl

theorem cell23_4615608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_4615608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615608 prefixEnd_4615608 := by exact prefixLift 4615608
  have htrace : WordTrace (prefixWord ++ tailWord_4615608) baseStart_4615608 baseEnd_4615608 := by
    simpa [prefixWord, tailWord_4615608, baseEnd_4615608] using wordTrace_append hprefix tailTrace_4615608
  have hstable : (prefixWord ++ tailWord_4615608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615608).length < 2 ^ (prefixWord ++ tailWord_4615608).sum := by decide
  have hdescent : baseEnd_4615608 < baseStart_4615608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615612 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4615612 : Nat := 118140960795 + 4615612 * 2 ^ 59
def prefixEnd_4615612 : Nat := 4983230072969 + 3 ^ 40 * 4615612 * 2
def baseEnd_4615612 : Nat := 2370027470660100630523193

theorem tailTrace_4615612 : CollatzResearch.WordTrace tailWord_4615612 prefixEnd_4615612 2370027470660100630523193 := by
  unfold tailWord_4615612
  simp only [CollatzResearch.WordTrace]
  refine ⟨84172599877216741308116545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112230133169622321744155393 84172599877216741308116545)
  ·
    refine ⟨63129449907912555981087409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84172599877216741308116545 63129449907912555981087409)
    ·
      refine ⟨47347087430934416985815557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63129449907912555981087409 47347087430934416985815557)
      ·
        refine ⟨8877578893300203184840417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47347087430934416985815557 8877578893300203184840417)
        ·
          refine ⟨6658184169975152388630313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8877578893300203184840417 6658184169975152388630313)
          ·
            refine ⟨4993638127481364291472735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6658184169975152388630313 4993638127481364291472735)
            ·
              refine ⟨7490457191222046437209103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4993638127481364291472735 7490457191222046437209103)
              ·
                refine ⟨11235685786833069655813655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7490457191222046437209103 11235685786833069655813655)
                ·
                  refine ⟨16853528680249604483720483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11235685786833069655813655 16853528680249604483720483)
                  ·
                    refine ⟨25280293020374406725580725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16853528680249604483720483 25280293020374406725580725)
                    ·
                      refine ⟨2370027470660100630523193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25280293020374406725580725 2370027470660100630523193)
                      ·
                        rfl

theorem cell23_4615612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4615612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615612 prefixEnd_4615612 := by exact prefixLift 4615612
  have htrace : WordTrace (prefixWord ++ tailWord_4615612) baseStart_4615612 baseEnd_4615612 := by
    simpa [prefixWord, tailWord_4615612, baseEnd_4615612] using wordTrace_append hprefix tailTrace_4615612
  have hstable : (prefixWord ++ tailWord_4615612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615612).length < 2 ^ (prefixWord ++ tailWord_4615612).sum := by decide
  have hdescent : baseEnd_4615612 < baseStart_4615612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615621 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_4615621 : Nat := 118140960795 + 4615621 * 2 ^ 59
def prefixEnd_4615621 : Nat := 4983230072969 + 3 ^ 40 * 4615621 * 2
def baseEnd_4615621 : Nat := 2370032091985991095310651

theorem tailTrace_4615621 : CollatzResearch.WordTrace tailWord_4615621 prefixEnd_4615621 2370032091985991095310651 := by
  unfold tailWord_4615621
  simp only [CollatzResearch.WordTrace]
  refine ⟨168345528011400877153310717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112230352007600584768873811 168345528011400877153310717)
  ·
    refine ⟨63129573004275328932491519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168345528011400877153310717 63129573004275328932491519)
    ·
      refine ⟨94694359506412993398737279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63129573004275328932491519 94694359506412993398737279)
      ·
        refine ⟨142041539259619490098105919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94694359506412993398737279 142041539259619490098105919)
        ·
          refine ⟨213062308889429235147158879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142041539259619490098105919 213062308889429235147158879)
          ·
            refine ⟨319593463334143852720738319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213062308889429235147158879 319593463334143852720738319)
            ·
              refine ⟨479390195001215779081107479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319593463334143852720738319 479390195001215779081107479)
              ·
                refine ⟨719085292501823668621661219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479390195001215779081107479 719085292501823668621661219)
                ·
                  refine ⟨1078627938752735502932491829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719085292501823668621661219 1078627938752735502932491829)
                  ·
                    refine ⟨101121369258068953399921109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1078627938752735502932491829 101121369258068953399921109)
                    ·
                      refine ⟨2370032091985991095310651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101121369258068953399921109 2370032091985991095310651)
                      ·
                        rfl

theorem cell23_4615621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_4615621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615621 prefixEnd_4615621 := by exact prefixLift 4615621
  have htrace : WordTrace (prefixWord ++ tailWord_4615621) baseStart_4615621 baseEnd_4615621 := by
    simpa [prefixWord, tailWord_4615621, baseEnd_4615621] using wordTrace_append hprefix tailTrace_4615621
  have hstable : (prefixWord ++ tailWord_4615621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615621).length < 2 ^ (prefixWord ++ tailWord_4615621).sum := by decide
  have hdescent : baseEnd_4615621 < baseStart_4615621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615626 : List Nat := [3, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2]
def baseStart_4615626 : Nat := 118140960795 + 4615626 * 2 ^ 59
def prefixEnd_4615626 : Nat := 4983230072969 + 3 ^ 40 * 4615626 * 2
def baseEnd_4615626 : Nat := 2370034659389263575748129

theorem tailTrace_4615626 : CollatzResearch.WordTrace tailWord_4615626 prefixEnd_4615626 2370034659389263575748129 := by
  unfold tailWord_4615626
  simp only [CollatzResearch.WordTrace]
  refine ⟨42086427594095690751810683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112230473584255175338161821 42086427594095690751810683)
  ·
    refine ⟨63129641391143536127716025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42086427594095690751810683 63129641391143536127716025)
    ·
      refine ⟨47347231043357652095787019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63129641391143536127716025 47347231043357652095787019)
      ·
        refine ⟨71020846565036478143680529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47347231043357652095787019 71020846565036478143680529)
        ·
          refine ⟨53265634923777358607760397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71020846565036478143680529 53265634923777358607760397)
          ·
            refine ⟨19974613096416509477910149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53265634923777358607760397 19974613096416509477910149)
            ·
              refine ⟨3745239955578095527108153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19974613096416509477910149 3745239955578095527108153)
              ·
                refine ⟨2808929966683571645331115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3745239955578095527108153 2808929966683571645331115)
                ·
                  refine ⟨4213394950025357467996673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808929966683571645331115 4213394950025357467996673)
                  ·
                    refine ⟨3160046212519018100997505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4213394950025357467996673 3160046212519018100997505)
                    ·
                      refine ⟨2370034659389263575748129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160046212519018100997505 2370034659389263575748129)
                      ·
                        rfl

theorem cell23_4615626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_4615626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615626 prefixEnd_4615626 := by exact prefixLift 4615626
  have htrace : WordTrace (prefixWord ++ tailWord_4615626) baseStart_4615626 baseEnd_4615626 := by
    simpa [prefixWord, tailWord_4615626, baseEnd_4615626] using wordTrace_append hprefix tailTrace_4615626
  have hstable : (prefixWord ++ tailWord_4615626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615626).length < 2 ^ (prefixWord ++ tailWord_4615626).sum := by decide
  have hdescent : baseEnd_4615626 < baseStart_4615626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615628 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_4615628 : Nat := 118140960795 + 4615628 * 2 ^ 59
def prefixEnd_4615628 : Nat := 4983230072969 + 3 ^ 40 * 4615628 * 2
def baseEnd_4615628 : Nat := 790011895450190855974373

theorem tailTrace_4615628 : CollatzResearch.WordTrace tailWord_4615628 prefixEnd_4615628 790011895450190855974373 := by
  unfold tailWord_4615628
  simp only [CollatzResearch.WordTrace]
  refine ⟨84172891661187758674407769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112230522214917011565877025 84172891661187758674407769)
  ·
    refine ⟨63129668745890819005805827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84172891661187758674407769 63129668745890819005805827)
    ·
      refine ⟨94694503118836228508708741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63129668745890819005805827 94694503118836228508708741)
      ·
        refine ⟨17755219334781792845382889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94694503118836228508708741 17755219334781792845382889)
        ·
          refine ⟨13316414501086344634037167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17755219334781792845382889 13316414501086344634037167)
          ·
            refine ⟨19974621751629516951055751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13316414501086344634037167 19974621751629516951055751)
            ·
              refine ⟨29961932627444275426583627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19974621751629516951055751 29961932627444275426583627)
              ·
                refine ⟨44942898941166413139875441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29961932627444275426583627 44942898941166413139875441)
                ·
                  refine ⟨33707174205874809854906581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44942898941166413139875441 33707174205874809854906581)
                  ·
                    refine ⟨790011895450190855974373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33707174205874809854906581 790011895450190855974373)
                    ·
                      rfl

theorem cell23_4615628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_4615628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615628 prefixEnd_4615628 := by exact prefixLift 4615628
  have htrace : WordTrace (prefixWord ++ tailWord_4615628) baseStart_4615628 baseEnd_4615628 := by
    simpa [prefixWord, tailWord_4615628, baseEnd_4615628] using wordTrace_append hprefix tailTrace_4615628
  have hstable : (prefixWord ++ tailWord_4615628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615628).length < 2 ^ (prefixWord ++ tailWord_4615628).sum := by decide
  have hdescent : baseEnd_4615628 < baseStart_4615628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615642 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3]
def baseStart_4615642 : Nat := 118140960795 + 4615642 * 2 ^ 59
def prefixEnd_4615642 : Nat := 4983230072969 + 3 ^ 40 * 4615642 * 2
def baseEnd_4615642 : Nat := 2370042875079735513148055

theorem tailTrace_4615642 : CollatzResearch.WordTrace tailWord_4615642 prefixEnd_4615642 2370042875079735513148055 := by
  unfold tailWord_4615642
  simp only [CollatzResearch.WordTrace]
  refine ⟨42086573486081199434956295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112230862629549865159883453 42086573486081199434956295)
  ·
    refine ⟨63129860229121799152434443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42086573486081199434956295 63129860229121799152434443)
    ·
      refine ⟨94694790343682698728651665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63129860229121799152434443 94694790343682698728651665)
      ·
        refine ⟨71021092757762024046488749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94694790343682698728651665 71021092757762024046488749)
        ·
          refine ⟨26632909784160759017433281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71021092757762024046488749 26632909784160759017433281)
          ·
            refine ⟨19974682338120569263074961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26632909784160759017433281 19974682338120569263074961)
            ·
              refine ⟨14981011753590426947306221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19974682338120569263074961 14981011753590426947306221)
              ·
                refine ⟨5617879407596410105239833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14981011753590426947306221 5617879407596410105239833)
                ·
                  refine ⟨4213409555697307578929875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5617879407596410105239833 4213409555697307578929875)
                  ·
                    refine ⟨6320114333545961368394813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4213409555697307578929875 6320114333545961368394813)
                    ·
                      refine ⟨2370042875079735513148055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6320114333545961368394813 2370042875079735513148055)
                      ·
                        rfl

theorem cell23_4615642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_4615642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615642 prefixEnd_4615642 := by exact prefixLift 4615642
  have htrace : WordTrace (prefixWord ++ tailWord_4615642) baseStart_4615642 baseEnd_4615642 := by
    simpa [prefixWord, tailWord_4615642, baseEnd_4615642] using wordTrace_append hprefix tailTrace_4615642
  have hstable : (prefixWord ++ tailWord_4615642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615642).length < 2 ^ (prefixWord ++ tailWord_4615642).sum := by decide
  have hdescent : baseEnd_4615642 < baseStart_4615642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615688 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 7]
def baseStart_4615688 : Nat := 118140960795 + 4615688 * 2 ^ 59
def prefixEnd_4615688 : Nat := 4983230072969 + 3 ^ 40 * 4615688 * 2
def baseEnd_4615688 : Nat := 263340721687760259241427

theorem tailTrace_4615688 : CollatzResearch.WordTrace tailWord_4615688 prefixEnd_4615688 263340721687760259241427 := by
  unfold tailWord_4615688
  simp only [CollatzResearch.WordTrace]
  refine ⟨84173985851079073797999859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112231981134772098397333145 84173985851079073797999859)
  ·
    refine ⟨126260978776618610696999789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84173985851079073797999859 126260978776618610696999789)
    ·
      refine ⟨47347867041231979011374921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126260978776618610696999789 47347867041231979011374921)
      ·
        refine ⟨35510900280923984258531191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47347867041231979011374921 35510900280923984258531191)
        ·
          refine ⟨53266350421385976387796787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35510900280923984258531191 53266350421385976387796787)
          ·
            refine ⟨79899525632078964581695181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53266350421385976387796787 79899525632078964581695181)
            ·
              refine ⟨29962322112029611718135693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79899525632078964581695181 29962322112029611718135693)
              ·
                refine ⟨11235870792011104394300885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29962322112029611718135693 11235870792011104394300885)
                ·
                  refine ⟨263340721687760259241427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11235870792011104394300885 263340721687760259241427)
                  ·
                    rfl

theorem cell23_4615688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 7].length) (baseStart_4615688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615688 prefixEnd_4615688 := by exact prefixLift 4615688
  have htrace : WordTrace (prefixWord ++ tailWord_4615688) baseStart_4615688 baseEnd_4615688 := by
    simpa [prefixWord, tailWord_4615688, baseEnd_4615688] using wordTrace_append hprefix tailTrace_4615688
  have hstable : (prefixWord ++ tailWord_4615688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615688).length < 2 ^ (prefixWord ++ tailWord_4615688).sum := by decide
  have hdescent : baseEnd_4615688 < baseStart_4615688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615693 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4615693 : Nat := 118140960795 + 4615693 * 2 ^ 59
def prefixEnd_4615693 : Nat := 4983230072969 + 3 ^ 40 * 4615693 * 2
def baseEnd_4615693 : Nat := 2370069062593114813610321

theorem tailTrace_4615693 : CollatzResearch.WordTrace tailWord_4615693 prefixEnd_4615693 2370069062593114813610321 := by
  unfold tailWord_4615693
  simp only [CollatzResearch.WordTrace]
  refine ⟨168348154067140033449931733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112232102711426688966621155 168348154067140033449931733)
  ·
    refine ⟨3945659860948594533982775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 168348154067140033449931733 3945659860948594533982775)
    ·
      refine ⟨5918489791422891800974163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3945659860948594533982775 5918489791422891800974163)
      ·
        refine ⟨8877734687134337701461245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5918489791422891800974163 8877734687134337701461245)
        ·
          refine ⟨3329150507675376638047967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8877734687134337701461245 3329150507675376638047967)
          ·
            refine ⟨4993725761513064957071951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3329150507675376638047967 4993725761513064957071951)
            ·
              refine ⟨7490588642269597435607927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4993725761513064957071951 7490588642269597435607927)
              ·
                refine ⟨11235882963404396153411891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7490588642269597435607927 11235882963404396153411891)
                ·
                  refine ⟨16853824445106594230117837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11235882963404396153411891 16853824445106594230117837)
                  ·
                    refine ⟨6320184166914972836294189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16853824445106594230117837 6320184166914972836294189)
                    ·
                      refine ⟨2370069062593114813610321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6320184166914972836294189 2370069062593114813610321)
                      ·
                        rfl

theorem cell23_4615693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4615693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615693 prefixEnd_4615693 := by exact prefixLift 4615693
  have htrace : WordTrace (prefixWord ++ tailWord_4615693) baseStart_4615693 baseEnd_4615693 := by
    simpa [prefixWord, tailWord_4615693, baseEnd_4615693] using wordTrace_append hprefix tailTrace_4615693
  have hstable : (prefixWord ++ tailWord_4615693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615693).length < 2 ^ (prefixWord ++ tailWord_4615693).sum := by decide
  have hdescent : baseEnd_4615693 < baseStart_4615693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615728 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_4615728 : Nat := 118140960795 + 4615728 * 2 ^ 59
def prefixEnd_4615728 : Nat := 4983230072969 + 3 ^ 40 * 4615728 * 2
def baseEnd_4615728 : Nat := 2370087034416022176672659

theorem tailTrace_4615728 : CollatzResearch.WordTrace tailWord_4615728 prefixEnd_4615728 2370087034416022176672659 := by
  unfold tailWord_4615728
  simp only [CollatzResearch.WordTrace]
  refine ⟨84174715311006617213727919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112232953748008822951637225 84174715311006617213727919)
  ·
    refine ⟨126262072966509925820591879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84174715311006617213727919 126262072966509925820591879)
    ·
      refine ⟨189393109449764888730887819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126262072966509925820591879 189393109449764888730887819)
      ·
        refine ⟨284089664174647333096331729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189393109449764888730887819 284089664174647333096331729)
        ·
          refine ⟨213067248130985499822248797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284089664174647333096331729 213067248130985499822248797)
          ·
            refine ⟨79900218049119562433343299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213067248130985499822248797 79900218049119562433343299)
            ·
              refine ⟨119850327073679343650014949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79900218049119562433343299 119850327073679343650014949)
              ·
                refine ⟨22471936326314876934377803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119850327073679343650014949 22471936326314876934377803)
                ·
                  refine ⟨33707904489472315401566705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22471936326314876934377803 33707904489472315401566705)
                  ·
                    refine ⟨25280928367104236551175029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33707904489472315401566705 25280928367104236551175029)
                    ·
                      refine ⟨2370087034416022176672659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25280928367104236551175029 2370087034416022176672659)
                      ·
                        rfl

theorem cell23_4615728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_4615728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615728 prefixEnd_4615728 := by exact prefixLift 4615728
  have htrace : WordTrace (prefixWord ++ tailWord_4615728) baseStart_4615728 baseEnd_4615728 := by
    simpa [prefixWord, tailWord_4615728, baseEnd_4615728] using wordTrace_append hprefix tailTrace_4615728
  have hstable : (prefixWord ++ tailWord_4615728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615728).length < 2 ^ (prefixWord ++ tailWord_4615728).sum := by decide
  have hdescent : baseEnd_4615728 < baseStart_4615728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615735 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 2, 5]
def baseStart_4615735 : Nat := 118140960795 + 4615735 * 2 ^ 59
def prefixEnd_4615735 : Nat := 4983230072969 + 3 ^ 40 * 4615735 * 2
def baseEnd_4615735 : Nat := 790030209593534549761709

theorem tailTrace_4615735 : CollatzResearch.WordTrace tailWord_4615735 prefixEnd_4615735 790030209593534549761709 := by
  unfold tailWord_4615735
  simp only [CollatzResearch.WordTrace]
  refine ⟨168349685932987874622960659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112233123955325249748640439 168349685932987874622960659)
  ·
    refine ⟨252524528899481811934440989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168349685932987874622960659 252524528899481811934440989)
    ·
      refine ⟨94696698337305679475415371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252524528899481811934440989 94696698337305679475415371)
      ·
        refine ⟨142045047505958519213123057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94696698337305679475415371 142045047505958519213123057)
        ·
          refine ⟨106533785629468889409842293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142045047505958519213123057 106533785629468889409842293)
          ·
            refine ⟨9987542402762708382172715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106533785629468889409842293 9987542402762708382172715)
            ·
              refine ⟨14981313604144062573259073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9987542402762708382172715 14981313604144062573259073)
              ·
                refine ⟨11235985203108046929944305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14981313604144062573259073 11235985203108046929944305)
                ·
                  refine ⟨8426988902331035197458229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11235985203108046929944305 8426988902331035197458229)
                  ·
                    refine ⟨790030209593534549761709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8426988902331035197458229 790030209593534549761709)
                    ·
                      rfl

theorem cell23_4615735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_4615735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615735 prefixEnd_4615735 := by exact prefixLift 4615735
  have htrace : WordTrace (prefixWord ++ tailWord_4615735) baseStart_4615735 baseEnd_4615735 := by
    simpa [prefixWord, tailWord_4615735, baseEnd_4615735] using wordTrace_append hprefix tailTrace_4615735
  have hstable : (prefixWord ++ tailWord_4615735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615735).length < 2 ^ (prefixWord ++ tailWord_4615735).sum := by decide
  have hdescent : baseEnd_4615735 < baseStart_4615735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615745 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4615745 : Nat := 118140960795 + 4615745 * 2 ^ 59
def prefixEnd_4615745 : Nat := 4983230072969 + 3 ^ 40 * 4615745 * 2
def baseEnd_4615745 : Nat := 2370095763587148610160081

theorem tailTrace_4615745 : CollatzResearch.WordTrace tailWord_4615745 prefixEnd_4615745 2370095763587148610160081 := by
  unfold tailWord_4615745
  simp only [CollatzResearch.WordTrace]
  refine ⟨168350050662951646330824689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112233367108634430887216459 168350050662951646330824689)
  ·
    refine ⟨126262537997213734748118517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168350050662951646330824689 126262537997213734748118517)
    ·
      refine ⟨11837112937238787632636111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126262537997213734748118517 11837112937238787632636111)
      ·
        refine ⟨17755669405858181448954167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11837112937238787632636111 17755669405858181448954167)
        ·
          refine ⟨26633504108787272173431251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17755669405858181448954167 26633504108787272173431251)
          ·
            refine ⟨39950256163180908260146877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26633504108787272173431251 39950256163180908260146877)
            ·
              refine ⟨14981346061192840597555079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39950256163180908260146877 14981346061192840597555079)
              ·
                refine ⟨22472019091789260896332619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14981346061192840597555079 22472019091789260896332619)
                ·
                  refine ⟨33708028637683891344498929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22472019091789260896332619 33708028637683891344498929)
                  ·
                    refine ⟨25281021478262918508374197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33708028637683891344498929 25281021478262918508374197)
                    ·
                      refine ⟨2370095763587148610160081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25281021478262918508374197 2370095763587148610160081)
                      ·
                        rfl

theorem cell23_4615745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4615745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615745 prefixEnd_4615745 := by exact prefixLift 4615745
  have htrace : WordTrace (prefixWord ++ tailWord_4615745) baseStart_4615745 baseEnd_4615745 := by
    simpa [prefixWord, tailWord_4615745, baseEnd_4615745] using wordTrace_append hprefix tailTrace_4615745
  have hstable : (prefixWord ++ tailWord_4615745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615745).length < 2 ^ (prefixWord ++ tailWord_4615745).sum := by decide
  have hdescent : baseEnd_4615745 < baseStart_4615745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615755 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 1, 6, 2]
def baseStart_4615755 : Nat := 118140960795 + 4615755 * 2 ^ 59
def prefixEnd_4615755 : Nat := 4983230072969 + 3 ^ 40 * 4615755 * 2
def baseEnd_4615755 : Nat := 2370100898393693571035035

theorem tailTrace_4615755 : CollatzResearch.WordTrace tailWord_4615755 prefixEnd_4615755 2370100898393693571035035 := by
  unfold tailWord_4615755
  simp only [CollatzResearch.WordTrace]
  refine ⟨168350415392915418038688719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112233610261943612025792479 168350415392915418038688719)
  ·
    refine ⟨252525623089373127058033079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168350415392915418038688719 252525623089373127058033079)
    ·
      refine ⟨378788434634059690587049619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252525623089373127058033079 378788434634059690587049619)
      ·
        refine ⟨568182651951089535880574429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378788434634059690587049619 568182651951089535880574429)
        ·
          refine ⟨213068494481658575955215411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 568182651951089535880574429 213068494481658575955215411)
          ·
            refine ⟨319602741722487863932823117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213068494481658575955215411 319602741722487863932823117)
            ·
              refine ⟨119851028145932948974808669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 319602741722487863932823117 119851028145932948974808669)
              ·
                refine ⟨44944135554724855865553251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119851028145932948974808669 44944135554724855865553251)
                ·
                  refine ⟨67416203332087283798329877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44944135554724855865553251 67416203332087283798329877)
                  ·
                    refine ⟨3160134531191591428046713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67416203332087283798329877 3160134531191591428046713)
                    ·
                      refine ⟨2370100898393693571035035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160134531191591428046713 2370100898393693571035035)
                      ·
                        rfl

theorem cell23_4615755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 6, 2].length) (baseStart_4615755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615755 prefixEnd_4615755 := by exact prefixLift 4615755
  have htrace : WordTrace (prefixWord ++ tailWord_4615755) baseStart_4615755 baseEnd_4615755 := by
    simpa [prefixWord, tailWord_4615755, baseEnd_4615755] using wordTrace_append hprefix tailTrace_4615755
  have hstable : (prefixWord ++ tailWord_4615755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615755).length < 2 ^ (prefixWord ++ tailWord_4615755).sum := by decide
  have hdescent : baseEnd_4615755 < baseStart_4615755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615765 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_4615765 : Nat := 118140960795 + 4615765 * 2 ^ 59
def prefixEnd_4615765 : Nat := 4983230072969 + 3 ^ 40 * 4615765 * 2
def baseEnd_4615765 : Nat := 790035344400079510636663

theorem tailTrace_4615765 : CollatzResearch.WordTrace tailWord_4615765 prefixEnd_4615765 790035344400079510636663 := by
  unfold tailWord_4615765
  simp only [CollatzResearch.WordTrace]
  refine ⟨168350780122879189746552749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112233853415252793164368499 168350780122879189746552749)
  ·
    refine ⟨63131542546079696154957281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168350780122879189746552749 63131542546079696154957281)
    ·
      refine ⟨47348656909559772116217961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63131542546079696154957281 47348656909559772116217961)
      ·
        refine ⟨35511492682169829087163471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47348656909559772116217961 35511492682169829087163471)
        ·
          refine ⟨53267239023254743630745207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35511492682169829087163471 53267239023254743630745207)
          ·
            refine ⟨79900858534882115446117811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53267239023254743630745207 79900858534882115446117811)
            ·
              refine ⟨119851287802323173169176717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79900858534882115446117811 119851287802323173169176717)
              ·
                refine ⟨44944232925871189938441269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119851287802323173169176717 44944232925871189938441269)
                ·
                  refine ⟨4213521836800424056728869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44944232925871189938441269 4213521836800424056728869)
                  ·
                    refine ⟨790035344400079510636663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4213521836800424056728869 790035344400079510636663)
                    ·
                      rfl

theorem cell23_4615765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_4615765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615765 prefixEnd_4615765 := by exact prefixLift 4615765
  have htrace : WordTrace (prefixWord ++ tailWord_4615765) baseStart_4615765 baseEnd_4615765 := by
    simpa [prefixWord, tailWord_4615765, baseEnd_4615765] using wordTrace_append hprefix tailTrace_4615765
  have hstable : (prefixWord ++ tailWord_4615765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615765).length < 2 ^ (prefixWord ++ tailWord_4615765).sum := by decide
  have hdescent : baseEnd_4615765 < baseStart_4615765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615768 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_4615768 : Nat := 118140960795 + 4615768 * 2 ^ 59
def prefixEnd_4615768 : Nat := 4983230072969 + 3 ^ 40 * 4615768 * 2
def baseEnd_4615768 : Nat := 2370107573642202020172475

theorem tailTrace_4615768 : CollatzResearch.WordTrace tailWord_4615768 prefixEnd_4615768 2370107573642202020172475 := by
  unfold tailWord_4615768
  simp only [CollatzResearch.WordTrace]
  refine ⟨84175444770934160629455979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112233926361245547505941305 84175444770934160629455979)
  ·
    refine ⟨126263167156401240944183969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84175444770934160629455979 126263167156401240944183969)
    ·
      refine ⟨94697375367300930708137977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126263167156401240944183969 94697375367300930708137977)
      ·
        refine ⟨71023031525475698031103483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94697375367300930708137977 71023031525475698031103483)
        ·
          refine ⟨106534547288213547046655225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71023031525475698031103483 106534547288213547046655225)
          ·
            refine ⟨79900910466160160284991419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106534547288213547046655225 79900910466160160284991419)
            ·
              refine ⟨119851365699240240427487129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79900910466160160284991419 119851365699240240427487129)
              ·
                refine ⟨89888524274430180320615347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119851365699240240427487129 89888524274430180320615347)
                ·
                  refine ⟨134832786411645270480923021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89888524274430180320615347 134832786411645270480923021)
                  ·
                    refine ⟨50562294904366976430346133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134832786411645270480923021 50562294904366976430346133)
                    ·
                      refine ⟨2370107573642202020172475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50562294904366976430346133 2370107573642202020172475)
                      ·
                        rfl

theorem cell23_4615768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_4615768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615768 prefixEnd_4615768 := by exact prefixLift 4615768
  have htrace : WordTrace (prefixWord ++ tailWord_4615768) baseStart_4615768 baseEnd_4615768 := by
    simpa [prefixWord, tailWord_4615768, baseEnd_4615768] using wordTrace_append hprefix tailTrace_4615768
  have hstable : (prefixWord ++ tailWord_4615768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615768).length < 2 ^ (prefixWord ++ tailWord_4615768).sum := by decide
  have hdescent : baseEnd_4615768 < baseStart_4615768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615772 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4615772 : Nat := 118140960795 + 4615772 * 2 ^ 59
def prefixEnd_4615772 : Nat := 4983230072969 + 3 ^ 40 * 4615772 * 2
def baseEnd_4615772 : Nat := 2370109627564820004522457

theorem tailTrace_4615772 : CollatzResearch.WordTrace tailWord_4615772 prefixEnd_4615772 2370109627564820004522457 := by
  unfold tailWord_4615772
  simp only [CollatzResearch.WordTrace]
  refine ⟨84175517716926914971028785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112234023622569219961371713 84175517716926914971028785)
  ·
    refine ⟨63131638287695186228271589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84175517716926914971028785 63131638287695186228271589)
    ·
      refine ⟨11837182178942847417800923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63131638287695186228271589 11837182178942847417800923)
      ·
        refine ⟨17755773268414271126701385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11837182178942847417800923 17755773268414271126701385)
        ·
          refine ⟨13316829951310703345026039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17755773268414271126701385 13316829951310703345026039)
          ·
            refine ⟨19975244926966055017539059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13316829951310703345026039 19975244926966055017539059)
            ·
              refine ⟨29962867390449082526308589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19975244926966055017539059 29962867390449082526308589)
              ·
                refine ⟨11236075271418405947365721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29962867390449082526308589 11236075271418405947365721)
                ·
                  refine ⟨8427056453563804460524291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11236075271418405947365721 8427056453563804460524291)
                  ·
                    refine ⟨12640584680345706690786437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8427056453563804460524291 12640584680345706690786437)
                    ·
                      refine ⟨2370109627564820004522457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12640584680345706690786437 2370109627564820004522457)
                      ·
                        rfl

theorem cell23_4615772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4615772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615772 prefixEnd_4615772 := by exact prefixLift 4615772
  have htrace : WordTrace (prefixWord ++ tailWord_4615772) baseStart_4615772 baseEnd_4615772 := by
    simpa [prefixWord, tailWord_4615772, baseEnd_4615772] using wordTrace_append hprefix tailTrace_4615772
  have hstable : (prefixWord ++ tailWord_4615772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615772).length < 2 ^ (prefixWord ++ tailWord_4615772).sum := by decide
  have hdescent : baseEnd_4615772 < baseStart_4615772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615792 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 3]
def baseStart_4615792 : Nat := 118140960795 + 4615792 * 2 ^ 59
def prefixEnd_4615792 : Nat := 4983230072969 + 3 ^ 40 * 4615792 * 2
def baseEnd_4615792 : Nat := 2370119897177909926272365

theorem tailTrace_4615792 : CollatzResearch.WordTrace tailWord_4615792 prefixEnd_4615792 2370119897177909926272365 := by
  unfold tailWord_4615792
  simp only [CollatzResearch.WordTrace]
  refine ⟨84175882446890686678892815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112234509929187582238523753 84175882446890686678892815)
  ·
    refine ⟨126263823670336030018339223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84175882446890686678892815 126263823670336030018339223)
    ·
      refine ⟨189395735505504045027508835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126263823670336030018339223 189395735505504045027508835)
      ·
        refine ⟨284093603258256067541263253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189395735505504045027508835 284093603258256067541263253)
        ·
          refine ⟨13316887652730753165996715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 284093603258256067541263253 13316887652730753165996715)
          ·
            refine ⟨19975331479096129748995073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13316887652730753165996715 19975331479096129748995073)
            ·
              refine ⟨14981498609322097311746305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19975331479096129748995073 14981498609322097311746305)
              ·
                refine ⟨11236123956991572983809729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14981498609322097311746305 11236123956991572983809729)
                ·
                  refine ⟨8427092967743679737857297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11236123956991572983809729 8427092967743679737857297)
                  ·
                    refine ⟨6320319725807759803392973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8427092967743679737857297 6320319725807759803392973)
                    ·
                      refine ⟨2370119897177909926272365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6320319725807759803392973 2370119897177909926272365)
                      ·
                        rfl

theorem cell23_4615792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 3].length) (baseStart_4615792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615792 prefixEnd_4615792 := by exact prefixLift 4615792
  have htrace : WordTrace (prefixWord ++ tailWord_4615792) baseStart_4615792 baseEnd_4615792 := by
    simpa [prefixWord, tailWord_4615792, baseEnd_4615792] using wordTrace_append hprefix tailTrace_4615792
  have hstable : (prefixWord ++ tailWord_4615792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615792).length < 2 ^ (prefixWord ++ tailWord_4615792).sum := by decide
  have hdescent : baseEnd_4615792 < baseStart_4615792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615826 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_4615826 : Nat := 118140960795 + 4615826 * 2 ^ 59
def prefixEnd_4615826 : Nat := 4983230072969 + 3 ^ 40 * 4615826 * 2
def baseEnd_4615826 : Nat := 2370137355520162793247209

theorem tailTrace_4615826 : CollatzResearch.WordTrace tailWord_4615826 prefixEnd_4615826 2370137355520162793247209 := by
  unfold tailWord_4615826
  simp only [CollatzResearch.WordTrace]
  refine ⟨42088251243914549291130833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112235336650438798109682221 42088251243914549291130833)
  ·
    refine ⟨31566188432935911968348125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42088251243914549291130833 31566188432935911968348125)
    ·
      refine ⟨11837320662350966988130547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31566188432935911968348125 11837320662350966988130547)
      ·
        refine ⟨17755980993526450482195821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11837320662350966988130547 17755980993526450482195821)
        ·
          refine ⟨6658492872572418930823433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17755980993526450482195821 6658492872572418930823433)
          ·
            refine ⟨4993869654429314198117575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6658492872572418930823433 4993869654429314198117575)
            ·
              refine ⟨7490804481643971297176363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4993869654429314198117575 7490804481643971297176363)
              ·
                refine ⟨11236206722465956945764545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7490804481643971297176363 11236206722465956945764545)
                ·
                  refine ⟨8427155041849467709323409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11236206722465956945764545 8427155041849467709323409)
                  ·
                    refine ⟨6320366281387100781992557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8427155041849467709323409 6320366281387100781992557)
                    ·
                      refine ⟨2370137355520162793247209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6320366281387100781992557 2370137355520162793247209)
                      ·
                        rfl

theorem cell23_4615826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_4615826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615826 prefixEnd_4615826 := by exact prefixLift 4615826
  have htrace : WordTrace (prefixWord ++ tailWord_4615826) baseStart_4615826 baseEnd_4615826 := by
    simpa [prefixWord, tailWord_4615826, baseEnd_4615826] using wordTrace_append hprefix tailTrace_4615826
  have hstable : (prefixWord ++ tailWord_4615826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615826).length < 2 ^ (prefixWord ++ tailWord_4615826).sum := by decide
  have hdescent : baseEnd_4615826 < baseStart_4615826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615865 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_4615865 : Nat := 118140960795 + 4615865 * 2 ^ 59
def prefixEnd_4615865 : Nat := 4983230072969 + 3 ^ 40 * 4615865 * 2
def baseEnd_4615865 : Nat := 2370157381265688140659529

theorem tailTrace_4615865 : CollatzResearch.WordTrace tailWord_4615865 prefixEnd_4615865 2370157381265688140659529 := by
  unfold tailWord_4615865
  simp only [CollatzResearch.WordTrace]
  refine ⟨168354427422516906825193049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112236284948344604550128699 168354427422516906825193049)
  ·
    refine ⟨126265820566887680118894787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168354427422516906825193049 126265820566887680118894787)
    ·
      refine ⟨189398730850331520178342181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126265820566887680118894787 189398730850331520178342181)
      ·
        refine ⟨35512262034437160033439159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189398730850331520178342181 35512262034437160033439159)
        ·
          refine ⟨53268393051655740050158739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35512262034437160033439159 53268393051655740050158739)
          ·
            refine ⟨79902589577483610075238109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53268393051655740050158739 79902589577483610075238109)
            ·
              refine ⟨29963471091556353778214291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79902589577483610075238109 29963471091556353778214291)
              ·
                refine ⟨44945206637334530667321437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29963471091556353778214291 44945206637334530667321437)
                ·
                  refine ⟨16854452489000449000245539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44945206637334530667321437 16854452489000449000245539)
                  ·
                    refine ⟨25281678733500673500368309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16854452489000449000245539 25281678733500673500368309)
                    ·
                      refine ⟨2370157381265688140659529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25281678733500673500368309 2370157381265688140659529)
                      ·
                        rfl

theorem cell23_4615865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_4615865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615865 prefixEnd_4615865 := by exact prefixLift 4615865
  have htrace : WordTrace (prefixWord ++ tailWord_4615865) baseStart_4615865 baseEnd_4615865 := by
    simpa [prefixWord, tailWord_4615865, baseEnd_4615865] using wordTrace_append hprefix tailTrace_4615865
  have hstable : (prefixWord ++ tailWord_4615865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615865).length < 2 ^ (prefixWord ++ tailWord_4615865).sum := by decide
  have hdescent : baseEnd_4615865 < baseStart_4615865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615879 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 3, 2, 2]
def baseStart_4615879 : Nat := 118140960795 + 4615879 * 2 ^ 59
def prefixEnd_4615879 : Nat := 4983230072969 + 3 ^ 40 * 4615879 * 2
def baseEnd_4615879 : Nat := 2370164569994851085884465

theorem tailTrace_4615879 : CollatzResearch.WordTrace tailWord_4615879 prefixEnd_4615879 2370164569994851085884465 := by
  unfold tailWord_4615879
  simp only [CollatzResearch.WordTrace]
  refine ⟨168354938044466187216202691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112236625362977458144135127 168354938044466187216202691)
  ·
    refine ⟨252532407066699280824304037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168354938044466187216202691 252532407066699280824304037)
    ·
      refine ⟨47349826325006115154557007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252532407066699280824304037 47349826325006115154557007)
      ·
        refine ⟨71024739487509172731835511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47349826325006115154557007 71024739487509172731835511)
        ·
          refine ⟨106537109231263759097753267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71024739487509172731835511 106537109231263759097753267)
          ·
            refine ⟨159805663846895638646629901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106537109231263759097753267 159805663846895638646629901)
            ·
              refine ⟨59927123942585864492486213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159805663846895638646629901 59927123942585864492486213)
              ·
                refine ⟨11236335739234849592341165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59927123942585864492486213 11236335739234849592341165)
                ·
                  refine ⟨4213625902213068597127937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11236335739234849592341165 4213625902213068597127937)
                  ·
                    refine ⟨3160219426659801447845953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4213625902213068597127937 3160219426659801447845953)
                    ·
                      refine ⟨2370164569994851085884465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160219426659801447845953 2370164569994851085884465)
                      ·
                        rfl

theorem cell23_4615879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_4615879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615879 prefixEnd_4615879 := by exact prefixLift 4615879
  have htrace : WordTrace (prefixWord ++ tailWord_4615879) baseStart_4615879 baseEnd_4615879 := by
    simpa [prefixWord, tailWord_4615879, baseEnd_4615879] using wordTrace_append hprefix tailTrace_4615879
  have hstable : (prefixWord ++ tailWord_4615879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615879).length < 2 ^ (prefixWord ++ tailWord_4615879).sum := by decide
  have hdescent : baseEnd_4615879 < baseStart_4615879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615945 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 4, 6]
def baseStart_4615945 : Nat := 118140960795 + 4615945 * 2 ^ 59
def prefixEnd_4615945 : Nat := 4983230072969 + 3 ^ 40 * 4615945 * 2
def baseEnd_4615945 : Nat := 790066153239349275886387

theorem tailTrace_4615945 : CollatzResearch.WordTrace tailWord_4615945 prefixEnd_4615945 790066153239349275886387 := by
  unfold tailWord_4615945
  simp only [CollatzResearch.WordTrace]
  refine ⟨168357345262227080488105289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112238230174818053658736859 168357345262227080488105289)
  ·
    refine ⟨126268008946670310366078967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168357345262227080488105289 126268008946670310366078967)
    ·
      refine ⟨189402013420005465549118451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126268008946670310366078967 189402013420005465549118451)
      ·
        refine ⟨284103020130008198323677677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189402013420005465549118451 284103020130008198323677677)
        ·
          refine ⟨106538632548753074371379129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284103020130008198323677677 106538632548753074371379129)
          ·
            refine ⟨79903974411564805778534347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106538632548753074371379129 79903974411564805778534347)
            ·
              refine ⟨119855961617347208667801521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79903974411564805778534347 119855961617347208667801521)
              ·
                refine ⟨89891971213010406500851141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119855961617347208667801521 89891971213010406500851141)
                ·
                  refine ⟨16854744602439451218909589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89891971213010406500851141 16854744602439451218909589)
                  ·
                    refine ⟨790066153239349275886387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16854744602439451218909589 790066153239349275886387)
                    ·
                      rfl

theorem cell23_4615945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_4615945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615945 prefixEnd_4615945 := by exact prefixLift 4615945
  have htrace : WordTrace (prefixWord ++ tailWord_4615945) baseStart_4615945 baseEnd_4615945 := by
    simpa [prefixWord, tailWord_4615945, baseEnd_4615945] using wordTrace_append hprefix tailTrace_4615945
  have hstable : (prefixWord ++ tailWord_4615945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615945).length < 2 ^ (prefixWord ++ tailWord_4615945).sum := by decide
  have hdescent : baseEnd_4615945 < baseStart_4615945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615955 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 5]
def baseStart_4615955 : Nat := 118140960795 + 4615955 * 2 ^ 59
def prefixEnd_4615955 : Nat := 4983230072969 + 3 ^ 40 * 4615955 * 2
def baseEnd_4615955 : Nat := 2370203594524592788534115

theorem tailTrace_4615955 : CollatzResearch.WordTrace tailWord_4615955 prefixEnd_4615955 2370203594524592788534115 := by
  unfold tailWord_4615955
  simp only [CollatzResearch.WordTrace]
  refine ⟨168357709992190852195969319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112238473328127234797312879 168357709992190852195969319)
  ·
    refine ⟨252536564988286278293953979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168357709992190852195969319 252536564988286278293953979)
    ·
      refine ⟨378804847482429417440930969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252536564988286278293953979 378804847482429417440930969)
      ·
        refine ⟨284103635611822063080698227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378804847482429417440930969 284103635611822063080698227)
        ·
          refine ⟨426155453417733094621047341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284103635611822063080698227 426155453417733094621047341)
          ·
            refine ⟨159808295031649910482892753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 426155453417733094621047341 159808295031649910482892753)
            ·
              refine ⟨119856221273737432862169565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159808295031649910482892753 119856221273737432862169565)
              ·
                refine ⟨44946082977651537323313587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119856221273737432862169565 44946082977651537323313587)
                ·
                  refine ⟨67419124466477305984970381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44946082977651537323313587 67419124466477305984970381)
                  ·
                    refine ⟨25282171674928989744363893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67419124466477305984970381 25282171674928989744363893)
                    ·
                      refine ⟨2370203594524592788534115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25282171674928989744363893 2370203594524592788534115)
                      ·
                        rfl

theorem cell23_4615955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_4615955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615955 prefixEnd_4615955 := by exact prefixLift 4615955
  have htrace : WordTrace (prefixWord ++ tailWord_4615955) baseStart_4615955 baseEnd_4615955 := by
    simpa [prefixWord, tailWord_4615955, baseEnd_4615955] using wordTrace_append hprefix tailTrace_4615955
  have hstable : (prefixWord ++ tailWord_4615955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615955).length < 2 ^ (prefixWord ++ tailWord_4615955).sum := by decide
  have hdescent : baseEnd_4615955 < baseStart_4615955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615986 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2]
def baseStart_4615986 : Nat := 118140960795 + 4615986 * 2 ^ 59
def prefixEnd_4615986 : Nat := 4983230072969 + 3 ^ 40 * 4615986 * 2
def baseEnd_4615986 : Nat := 2370219512424882167246473

theorem tailTrace_4615986 : CollatzResearch.WordTrace tailWord_4615986 prefixEnd_4615986 2370219512424882167246473 := by
  unfold tailWord_4615986
  simp only [CollatzResearch.WordTrace]
  refine ⟨42089710163769636122586953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112239227103385696326898541 42089710163769636122586953)
  ·
    refine ⟨31567282622827227091940215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42089710163769636122586953 31567282622827227091940215)
    ·
      refine ⟨47350923934240840637910323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31567282622827227091940215 47350923934240840637910323)
      ·
        refine ⟨71026385901361260956865485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47350923934240840637910323 71026385901361260956865485)
        ·
          refine ⟨26634894713010472858824557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71026385901361260956865485 26634894713010472858824557)
          ·
            refine ⟨9988085517378927322059209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26634894713010472858824557 9988085517378927322059209)
            ·
              refine ⟨7491064138034195491544407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9988085517378927322059209 7491064138034195491544407)
              ·
                refine ⟨11236596207051293237316611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7491064138034195491544407 11236596207051293237316611)
                ·
                  refine ⟨16854894310576939855974917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11236596207051293237316611 16854894310576939855974917)
                  ·
                    refine ⟨3160292683233176222995297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16854894310576939855974917 3160292683233176222995297)
                    ·
                      refine ⟨2370219512424882167246473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160292683233176222995297 2370219512424882167246473)
                      ·
                        rfl

theorem cell23_4615986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_4615986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615986 prefixEnd_4615986 := by exact prefixLift 4615986
  have htrace : WordTrace (prefixWord ++ tailWord_4615986) baseStart_4615986 baseEnd_4615986 := by
    simpa [prefixWord, tailWord_4615986, baseEnd_4615986] using wordTrace_append hprefix tailTrace_4615986
  have hstable : (prefixWord ++ tailWord_4615986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615986).length < 2 ^ (prefixWord ++ tailWord_4615986).sum := by decide
  have hdescent : baseEnd_4615986 < baseStart_4615986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615992 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 7]
def baseStart_4615992 : Nat := 118140960795 + 4615992 * 2 ^ 59
def prefixEnd_4615992 : Nat := 4983230072969 + 3 ^ 40 * 4615992 * 2
def baseEnd_4615992 : Nat := 263358065923201015974605

theorem tailTrace_4615992 : CollatzResearch.WordTrace tailWord_4615992 prefixEnd_4615992 263358065923201015974605 := by
  unfold tailWord_4615992
  simp only [CollatzResearch.WordTrace]
  refine ⟨84179529746528403757533115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112239372995371205010044153 84179529746528403757533115)
  ·
    refine ⟨126269294619792605636299673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84179529746528403757533115 126269294619792605636299673)
    ·
      refine ⟨94701970964844454227224755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126269294619792605636299673 94701970964844454227224755)
      ·
        refine ⟨142052956447266681340837133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94701970964844454227224755 142052956447266681340837133)
        ·
          refine ⟨53269858667725005502813925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142052956447266681340837133 53269858667725005502813925)
          ·
            refine ⟨9988098500198438531777611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53269858667725005502813925 9988098500198438531777611)
            ·
              refine ⟨14982147750297657797666417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9988098500198438531777611 14982147750297657797666417)
              ·
                refine ⟨11236610812723243348249813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14982147750297657797666417 11236610812723243348249813)
                ·
                  refine ⟨263358065923201015974605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11236610812723243348249813 263358065923201015974605)
                  ·
                    rfl

theorem cell23_4615992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 7].length) (baseStart_4615992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4615992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4615992 prefixEnd_4615992 := by exact prefixLift 4615992
  have htrace : WordTrace (prefixWord ++ tailWord_4615992) baseStart_4615992 baseEnd_4615992 := by
    simpa [prefixWord, tailWord_4615992, baseEnd_4615992] using wordTrace_append hprefix tailTrace_4615992
  have hstable : (prefixWord ++ tailWord_4615992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615992).length < 2 ^ (prefixWord ++ tailWord_4615992).sum := by decide
  have hdescent : baseEnd_4615992 < baseStart_4615992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616009 : List Nat := [1, 2, 1, 1, 2, 4, 4, 3, 5]
def baseStart_4616009 : Nat := 118140960795 + 4616009 * 2 ^ 59
def prefixEnd_4616009 : Nat := 4983230072969 + 3 ^ 40 * 4616009 * 2
def baseEnd_4616009 : Nat := 263359035831103953028763

theorem tailTrace_4616009 : CollatzResearch.WordTrace tailWord_4616009 prefixEnd_4616009 263359035831103953028763 := by
  unfold tailWord_4616009
  simp only [CollatzResearch.WordTrace]
  refine ⟨168359679533995219418435081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112239786355996812945623387 168359679533995219418435081)
  ·
    refine ⟨126269759650496414563826311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168359679533995219418435081 126269759650496414563826311)
    ·
      refine ⟨189404639475744621845739467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126269759650496414563826311 189404639475744621845739467)
      ·
        refine ⟨284106959213616932768609201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189404639475744621845739467 284106959213616932768609201)
        ·
          refine ⟨213080219410212699576456901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284106959213616932768609201 213080219410212699576456901)
          ·
            refine ⟨39952541139414881170585669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213080219410212699576456901 39952541139414881170585669)
            ·
              refine ⟨7491101463640290219484813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39952541139414881170585669 7491101463640290219484813)
              ·
                refine ⟨2809163048865108832306805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7491101463640290219484813 2809163048865108832306805)
                ·
                  refine ⟨263359035831103953028763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2809163048865108832306805 263359035831103953028763)
                  ·
                    rfl

theorem cell23_4616009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 5].length) (baseStart_4616009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616009 prefixEnd_4616009 := by exact prefixLift 4616009
  have htrace : WordTrace (prefixWord ++ tailWord_4616009) baseStart_4616009 baseEnd_4616009 := by
    simpa [prefixWord, tailWord_4616009, baseEnd_4616009] using wordTrace_append hprefix tailTrace_4616009
  have hstable : (prefixWord ++ tailWord_4616009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616009).length < 2 ^ (prefixWord ++ tailWord_4616009).sum := by decide
  have hdescent : baseEnd_4616009 < baseStart_4616009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616020 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_4616020 : Nat := 118140960795 + 4616020 * 2 ^ 59
def prefixEnd_4616020 : Nat := 4983230072969 + 3 ^ 40 * 4616020 * 2
def baseEnd_4616020 : Nat := 2370236970767135034221317

theorem tailTrace_4616020 : CollatzResearch.WordTrace tailWord_4616020 prefixEnd_4616020 2370236970767135034221317 := by
  unfold tailWord_4616020
  simp only [CollatzResearch.WordTrace]
  refine ⟨84180040368477684148542757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112240053824636912198057009 84180040368477684148542757)
  ·
    refine ⟨15783757569089565777851767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84180040368477684148542757 15783757569089565777851767)
    ·
      refine ⟨23675636353634348666777651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15783757569089565777851767 23675636353634348666777651)
      ·
        refine ⟨35513454530451523000166477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23675636353634348666777651 35513454530451523000166477)
        ·
          refine ⟨13317545448919321125062429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35513454530451523000166477 13317545448919321125062429)
          ·
            refine ⟨4994079543344745421898411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13317545448919321125062429 4994079543344745421898411)
            ·
              refine ⟨7491119315017118132847617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4994079543344745421898411 7491119315017118132847617)
              ·
                refine ⟨5618339486262838599635713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7491119315017118132847617 5618339486262838599635713)
                ·
                  refine ⟨4213754614697128949726785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5618339486262838599635713 4213754614697128949726785)
                  ·
                    refine ⟨3160315961022846712295089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4213754614697128949726785 3160315961022846712295089)
                    ·
                      refine ⟨2370236970767135034221317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160315961022846712295089 2370236970767135034221317)
                      ·
                        rfl

theorem cell23_4616020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_4616020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616020 prefixEnd_4616020 := by exact prefixLift 4616020
  have htrace : WordTrace (prefixWord ++ tailWord_4616020) baseStart_4616020 baseEnd_4616020 := by
    simpa [prefixWord, tailWord_4616020, baseEnd_4616020] using wordTrace_append hprefix tailTrace_4616020
  have hstable : (prefixWord ++ tailWord_4616020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616020).length < 2 ^ (prefixWord ++ tailWord_4616020).sum := by decide
  have hdescent : baseEnd_4616020 < baseStart_4616020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616122 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_4616122 : Nat := 118140960795 + 4616122 * 2 ^ 59
def prefixEnd_4616122 : Nat := 4983230072969 + 3 ^ 40 * 4616122 * 2
def baseEnd_4616122 : Nat := 2370289345793893635145847

theorem tailTrace_4616122 : CollatzResearch.WordTrace tailWord_4616122 prefixEnd_4616122 2370289345793893635145847 := by
  unfold tailWord_4616122
  simp only [CollatzResearch.WordTrace]
  refine ⟨42090950245646459929324655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112242533988390559811532413 42090950245646459929324655)
  ·
    refine ⟨63136425368469689893986983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42090950245646459929324655 63136425368469689893986983)
    ·
      refine ⟨94704638052704534840980475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63136425368469689893986983 94704638052704534840980475)
      ·
        refine ⟨142056957079056802261470713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94704638052704534840980475 142056957079056802261470713)
        ·
          refine ⟨106542717809292601696103035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142056957079056802261470713 106542717809292601696103035)
          ·
            refine ⟨159814076713938902544154553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106542717809292601696103035 159814076713938902544154553)
            ·
              refine ⟨119860557535454176908115915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159814076713938902544154553 119860557535454176908115915)
              ·
                refine ⟨179790836303181265362173873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119860557535454176908115915 179790836303181265362173873)
                ·
                  refine ⟨134843127227385949021630405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179790836303181265362173873 134843127227385949021630405)
                  ·
                    refine ⟨25283086355134865441555701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134843127227385949021630405 25283086355134865441555701)
                    ·
                      refine ⟨2370289345793893635145847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25283086355134865441555701 2370289345793893635145847)
                      ·
                        rfl

theorem cell23_4616122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_4616122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616122 prefixEnd_4616122 := by exact prefixLift 4616122
  have htrace : WordTrace (prefixWord ++ tailWord_4616122) baseStart_4616122 baseEnd_4616122 := by
    simpa [prefixWord, tailWord_4616122, baseEnd_4616122] using wordTrace_append hprefix tailTrace_4616122
  have hstable : (prefixWord ++ tailWord_4616122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616122).length < 2 ^ (prefixWord ++ tailWord_4616122).sum := by decide
  have hdescent : baseEnd_4616122 < baseStart_4616122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616143 : List Nat := [1, 1, 2, 1, 1, 5, 3, 4, 1, 1, 3]
def baseStart_4616143 : Nat := 118140960795 + 4616143 * 2 ^ 59
def prefixEnd_4616143 : Nat := 4983230072969 + 3 ^ 40 * 4616143 * 2
def baseEnd_4616143 : Nat := 2370300128887638052983251

theorem tailTrace_4616143 : CollatzResearch.WordTrace tailWord_4616143 prefixEnd_4616143 2370300128887638052983251 := by
  unfold tailWord_4616143
  simp only [CollatzResearch.WordTrace]
  refine ⟨168364566915509760303813083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112243044610339840202542055 168364566915509760303813083)
  ·
    refine ⟨252546850373264640455719625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168364566915509760303813083 252546850373264640455719625)
    ·
      refine ⟨189410137779948480341789719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252546850373264640455719625 189410137779948480341789719)
      ·
        refine ⟨284115206669922720512684579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189410137779948480341789719 284115206669922720512684579)
        ·
          refine ⟨426172810004884080769026869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284115206669922720512684579 426172810004884080769026869)
          ·
            refine ⟨39953700937957882572096269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 426172810004884080769026869 39953700937957882572096269)
            ·
              refine ⟨14982637851734205964536101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39953700937957882572096269 14982637851734205964536101)
              ·
                refine ⟨2809244597200163618350519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14982637851734205964536101 2809244597200163618350519)
                ·
                  refine ⟨4213866895800245427525779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809244597200163618350519 4213866895800245427525779)
                  ·
                    refine ⟨6320800343700368141288669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4213866895800245427525779 6320800343700368141288669)
                    ·
                      refine ⟨2370300128887638052983251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6320800343700368141288669 2370300128887638052983251)
                      ·
                        rfl

theorem cell23_4616143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 1, 1, 3].length) (baseStart_4616143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616143 prefixEnd_4616143 := by exact prefixLift 4616143
  have htrace : WordTrace (prefixWord ++ tailWord_4616143) baseStart_4616143 baseEnd_4616143 := by
    simpa [prefixWord, tailWord_4616143, baseEnd_4616143] using wordTrace_append hprefix tailTrace_4616143
  have hstable : (prefixWord ++ tailWord_4616143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616143).length < 2 ^ (prefixWord ++ tailWord_4616143).sum := by decide
  have hdescent : baseEnd_4616143 < baseStart_4616143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616159 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 1, 6]
def baseStart_4616159 : Nat := 118140960795 + 4616159 * 2 ^ 59
def prefixEnd_4616159 : Nat := 4983230072969 + 3 ^ 40 * 4616159 * 2
def baseEnd_4616159 : Nat := 790102781526036663461059

theorem tailTrace_4616159 : CollatzResearch.WordTrace tailWord_4616159 prefixEnd_4616159 790102781526036663461059 := by
  unfold tailWord_4616159
  simp only [CollatzResearch.WordTrace]
  refine ⟨168365150483451795036395531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112243433655634530024263687 168365150483451795036395531)
  ·
    refine ⟨252547725725177692554593297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168365150483451795036395531 252547725725177692554593297)
    ·
      refine ⟨189410794293883269415944973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252547725725177692554593297 189410794293883269415944973)
      ·
        refine ⟨71029047860206226030979365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189410794293883269415944973 71029047860206226030979365)
        ·
          refine ⟨13317946473788667380808631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71029047860206226030979365 13317946473788667380808631)
          ·
            refine ⟨19976919710683001071212947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13317946473788667380808631 19976919710683001071212947)
            ·
              refine ⟨29965379566024501606819421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19976919710683001071212947 29965379566024501606819421)
              ·
                refine ⟨11237017337259188102557283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29965379566024501606819421 11237017337259188102557283)
                ·
                  refine ⟨16855526005888782153835925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11237017337259188102557283 16855526005888782153835925)
                  ·
                    refine ⟨790102781526036663461059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16855526005888782153835925 790102781526036663461059)
                    ·
                      rfl

theorem cell23_4616159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_4616159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616159 prefixEnd_4616159 := by exact prefixLift 4616159
  have htrace : WordTrace (prefixWord ++ tailWord_4616159) baseStart_4616159 baseEnd_4616159 := by
    simpa [prefixWord, tailWord_4616159, baseEnd_4616159] using wordTrace_append hprefix tailTrace_4616159
  have hstable : (prefixWord ++ tailWord_4616159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616159).length < 2 ^ (prefixWord ++ tailWord_4616159).sum := by decide
  have hdescent : baseEnd_4616159 < baseStart_4616159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616172 : List Nat := [2, 2, 1, 1, 2, 1, 1, 13]
def baseStart_4616172 : Nat := 118140960795 + 4616172 * 2 ^ 59
def prefixEnd_4616172 : Nat := 4983230072969 + 3 ^ 40 * 4616172 * 2
def baseEnd_4616172 : Nat := 87789445178763645908171

theorem tailTrace_4616172 : CollatzResearch.WordTrace tailWord_4616172 prefixEnd_4616172 87789445178763645908171 := by
  unfold tailWord_4616172
  simp only [CollatzResearch.WordTrace]
  refine ⟨84182812316202349128309385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112243749754936465504412513 84182812316202349128309385)
  ·
    refine ⟨63137109237151761846232039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84182812316202349128309385 63137109237151761846232039)
    ·
      refine ⟨94705663855727642769348059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63137109237151761846232039 94705663855727642769348059)
      ·
        refine ⟨142058495783591464154022089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94705663855727642769348059 142058495783591464154022089)
        ·
          refine ⟨106543871837693598115516567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142058495783591464154022089 106543871837693598115516567)
          ·
            refine ⟨159815807756540397173274851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106543871837693598115516567 159815807756540397173274851)
            ·
              refine ⟨239723711634810595759912277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159815807756540397173274851 239723711634810595759912277)
              ·
                refine ⟨87789445178763645908171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 239723711634810595759912277 87789445178763645908171)
                ·
                  rfl

theorem cell23_4616172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 13].length) (baseStart_4616172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616172 prefixEnd_4616172 := by exact prefixLift 4616172
  have htrace : WordTrace (prefixWord ++ tailWord_4616172) baseStart_4616172 baseEnd_4616172 := by
    simpa [prefixWord, tailWord_4616172, baseEnd_4616172] using wordTrace_append hprefix tailTrace_4616172
  have hstable : (prefixWord ++ tailWord_4616172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616172).length < 2 ^ (prefixWord ++ tailWord_4616172).sum := by decide
  have hdescent : baseEnd_4616172 < baseStart_4616172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616200 : List Nat := [2, 1, 3, 2, 1, 2, 1, 6, 1, 2, 2]
def baseStart_4616200 : Nat := 118140960795 + 4616200 * 2 ^ 59
def prefixEnd_4616200 : Nat := 4983230072969 + 3 ^ 40 * 4616200 * 2
def baseEnd_4616200 : Nat := 2370329397284944329970489

theorem tailTrace_4616200 : CollatzResearch.WordTrace tailWord_4616200 prefixEnd_4616200 2370329397284944329970489 := by
  unfold tailWord_4616200
  simp only [CollatzResearch.WordTrace]
  refine ⟨84183322938151629519319027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112244430584202172692425369 84183322938151629519319027)
  ·
    refine ⟨126274984407227444278978541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84183322938151629519319027 126274984407227444278978541)
    ·
      refine ⟨47353119152710291604616953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126274984407227444278978541 47353119152710291604616953)
      ·
        refine ⟨35514839364532718703462715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47353119152710291604616953 35514839364532718703462715)
        ·
          refine ⟨53272259046799078055194073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35514839364532718703462715 53272259046799078055194073)
          ·
            refine ⟨39954194285099308541395555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53272259046799078055194073 39954194285099308541395555)
            ·
              refine ⟨59931291427648962812093333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39954194285099308541395555 59931291427648962812093333)
              ·
                refine ⟨2809279285671045131816875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59931291427648962812093333 2809279285671045131816875)
                ·
                  refine ⟨4213918928506567697725313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809279285671045131816875 4213918928506567697725313)
                  ·
                    refine ⟨3160439196379925773293985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4213918928506567697725313 3160439196379925773293985)
                    ·
                      refine ⟨2370329397284944329970489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160439196379925773293985 2370329397284944329970489)
                      ·
                        rfl

theorem cell23_4616200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_4616200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616200 prefixEnd_4616200 := by exact prefixLift 4616200
  have htrace : WordTrace (prefixWord ++ tailWord_4616200) baseStart_4616200 baseEnd_4616200 := by
    simpa [prefixWord, tailWord_4616200, baseEnd_4616200] using wordTrace_append hprefix tailTrace_4616200
  have hstable : (prefixWord ++ tailWord_4616200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616200).length < 2 ^ (prefixWord ++ tailWord_4616200).sum := by decide
  have hdescent : baseEnd_4616200 < baseStart_4616200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616213 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_4616213 : Nat := 118140960795 + 4616213 * 2 ^ 59
def prefixEnd_4616213 : Nat := 4983230072969 + 3 ^ 40 * 4616213 * 2
def baseEnd_4616213 : Nat := 2370336072533452779107929

theorem tailTrace_4616213 : CollatzResearch.WordTrace tailWord_4616213 prefixEnd_4616213 2370336072533452779107929 := by
  unfold tailWord_4616213
  simp only [CollatzResearch.WordTrace]
  refine ⟨168367120025256162258861293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112244746683504108172574195 168367120025256162258861293)
  ·
    refine ⟨63137670009471060847072985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168367120025256162258861293 63137670009471060847072985)
    ·
      refine ⟨47353252507103295635304739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63137670009471060847072985 47353252507103295635304739)
      ·
        refine ⟨71029878760654943452957109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47353252507103295635304739 71029878760654943452957109)
        ·
          refine ⟨6659051133811400948714729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71029878760654943452957109 6659051133811400948714729)
          ·
            refine ⟨4994288350358550711536047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6659051133811400948714729 4994288350358550711536047)
            ·
              refine ⟨7491432525537826067304071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4994288350358550711536047 7491432525537826067304071)
              ·
                refine ⟨11237148788306739100956107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7491432525537826067304071 11237148788306739100956107)
                ·
                  refine ⟨16855723182460108651434161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11237148788306739100956107 16855723182460108651434161)
                  ·
                    refine ⟨12641792386845081488575621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16855723182460108651434161 12641792386845081488575621)
                    ·
                      refine ⟨2370336072533452779107929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12641792386845081488575621 2370336072533452779107929)
                      ·
                        rfl

theorem cell23_4616213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_4616213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616213 prefixEnd_4616213 := by exact prefixLift 4616213
  have htrace : WordTrace (prefixWord ++ tailWord_4616213) baseStart_4616213 baseEnd_4616213 := by
    simpa [prefixWord, tailWord_4616213, baseEnd_4616213] using wordTrace_append hprefix tailTrace_4616213
  have hstable : (prefixWord ++ tailWord_4616213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616213).length < 2 ^ (prefixWord ++ tailWord_4616213).sum := by decide
  have hdescent : baseEnd_4616213 < baseStart_4616213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616229 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_4616229 : Nat := 118140960795 + 4616229 * 2 ^ 59
def prefixEnd_4616229 : Nat := 4983230072969 + 3 ^ 40 * 4616229 * 2
def baseEnd_4616229 : Nat := 2370344288223924716507855

theorem tailTrace_4616229 : CollatzResearch.WordTrace tailWord_4616229 prefixEnd_4616229 2370344288223924716507855 := by
  unfold tailWord_4616229
  simp only [CollatzResearch.WordTrace]
  refine ⟨168367703593198196991443741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112245135728798797994295827 168367703593198196991443741)
  ·
    refine ⟨63137888847449323871791403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168367703593198196991443741 63137888847449323871791403)
    ·
      refine ⟨94706833271173985807687105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63137888847449323871791403 94706833271173985807687105)
      ·
        refine ⟨71030124953380489355765329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94706833271173985807687105 71030124953380489355765329)
        ·
          refine ⟨53272593715035367016823997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71030124953380489355765329 53272593715035367016823997)
          ·
            refine ⟨19977222643138262631308999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53272593715035367016823997 19977222643138262631308999)
            ·
              refine ⟨29965833964707393946963499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19977222643138262631308999 29965833964707393946963499)
              ·
                refine ⟨44948750947061090920445249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29965833964707393946963499 44948750947061090920445249)
                ·
                  refine ⟨33711563210295818190333937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44948750947061090920445249 33711563210295818190333937)
                  ·
                    refine ⟨25283672407721863642750453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33711563210295818190333937 25283672407721863642750453)
                    ·
                      refine ⟨2370344288223924716507855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25283672407721863642750453 2370344288223924716507855)
                      ·
                        rfl

theorem cell23_4616229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_4616229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616229 prefixEnd_4616229 := by exact prefixLift 4616229
  have htrace : WordTrace (prefixWord ++ tailWord_4616229) baseStart_4616229 baseEnd_4616229 := by
    simpa [prefixWord, tailWord_4616229, baseEnd_4616229] using wordTrace_append hprefix tailTrace_4616229
  have hstable : (prefixWord ++ tailWord_4616229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616229).length < 2 ^ (prefixWord ++ tailWord_4616229).sum := by decide
  have hdescent : baseEnd_4616229 < baseStart_4616229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616234 : List Nat := [3, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_4616234 : Nat := 118140960795 + 4616234 * 2 ^ 59
def prefixEnd_4616234 : Nat := 4983230072969 + 3 ^ 40 * 4616234 * 2
def baseEnd_4616234 : Nat := 2370346855627197196945333

theorem tailTrace_4616234 : CollatzResearch.WordTrace tailWord_4616234 prefixEnd_4616234 2370346855627197196945333 := by
  unfold tailWord_4616234
  simp only [CollatzResearch.WordTrace]
  refine ⟨42091971489545020711343939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112245257305453388563583837 42091971489545020711343939)
  ·
    refine ⟨63137957234317531067015909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42091971489545020711343939 63137957234317531067015909)
    ·
      refine ⟨11838366981434537075065483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63137957234317531067015909 11838366981434537075065483)
      ·
        refine ⟨17757550472151805612598225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11838366981434537075065483 17757550472151805612598225)
        ·
          refine ⟨13318162854113854209448669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17757550472151805612598225 13318162854113854209448669)
          ·
            refine ⟨4994311070292695328543251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13318162854113854209448669 4994311070292695328543251)
            ·
              refine ⟨7491466605439042992814877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4994311070292695328543251 7491466605439042992814877)
              ·
                refine ⟨2809299977039641122305579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7491466605439042992814877 2809299977039641122305579)
                ·
                  refine ⟨4213949965559461683458369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809299977039641122305579 4213949965559461683458369)
                  ·
                    refine ⟨3160462474169596262593777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4213949965559461683458369 3160462474169596262593777)
                    ·
                      refine ⟨2370346855627197196945333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160462474169596262593777 2370346855627197196945333)
                      ·
                        rfl

theorem cell23_4616234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_4616234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616234 prefixEnd_4616234 := by exact prefixLift 4616234
  have htrace : WordTrace (prefixWord ++ tailWord_4616234) baseStart_4616234 baseEnd_4616234 := by
    simpa [prefixWord, tailWord_4616234, baseEnd_4616234] using wordTrace_append hprefix tailTrace_4616234
  have hstable : (prefixWord ++ tailWord_4616234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616234).length < 2 ^ (prefixWord ++ tailWord_4616234).sum := by decide
  have hdescent : baseEnd_4616234 < baseStart_4616234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616243 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 1, 3, 2]
def baseStart_4616243 : Nat := 118140960795 + 4616243 * 2 ^ 59
def prefixEnd_4616243 : Nat := 4983230072969 + 3 ^ 40 * 4616243 * 2
def baseEnd_4616243 : Nat := 2370351476953087661732791

theorem tailTrace_4616243 : CollatzResearch.WordTrace tailWord_4616243 prefixEnd_4616243 2370351476953087661732791 := by
  unfold tailWord_4616243
  simp only [CollatzResearch.WordTrace]
  refine ⟨168368214215147477382453383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112245476143431651588302255 168368214215147477382453383)
  ·
    refine ⟨252552321322721216073680075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168368214215147477382453383 252552321322721216073680075)
    ·
      refine ⟨378828481984081824110520113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252552321322721216073680075 378828481984081824110520113)
      ·
        refine ⟨284121361488061368082890085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378828481984081824110520113 284121361488061368082890085)
        ·
          refine ⟨53272755279011506515541891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 284121361488061368082890085 53272755279011506515541891)
          ·
            refine ⟨79909132918517259773312837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53272755279011506515541891 79909132918517259773312837)
            ·
              refine ⟨14982962422221986207496157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79909132918517259773312837 14982962422221986207496157)
              ·
                refine ⟨5618610908333244827811059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14982962422221986207496157 5618610908333244827811059)
                ·
                  refine ⟨8427916362499867241716589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5618610908333244827811059 8427916362499867241716589)
                  ·
                    refine ⟨3160468635937450215643721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8427916362499867241716589 3160468635937450215643721)
                    ·
                      refine ⟨2370351476953087661732791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160468635937450215643721 2370351476953087661732791)
                      ·
                        rfl

theorem cell23_4616243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 3, 2].length) (baseStart_4616243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616243 prefixEnd_4616243 := by exact prefixLift 4616243
  have htrace : WordTrace (prefixWord ++ tailWord_4616243) baseStart_4616243 baseEnd_4616243 := by
    simpa [prefixWord, tailWord_4616243, baseEnd_4616243] using wordTrace_append hprefix tailTrace_4616243
  have hstable : (prefixWord ++ tailWord_4616243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616243).length < 2 ^ (prefixWord ++ tailWord_4616243).sum := by decide
  have hdescent : baseEnd_4616243 < baseStart_4616243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616246 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_4616246 : Nat := 118140960795 + 4616246 * 2 ^ 59
def prefixEnd_4616246 : Nat := 4983230072969 + 3 ^ 40 * 4616246 * 2
def baseEnd_4616246 : Nat := 2370353017395051149995277

theorem tailTrace_4616246 : CollatzResearch.WordTrace tailWord_4616246 prefixEnd_4616246 2370353017395051149995277 := by
  unfold tailWord_4616246
  simp only [CollatzResearch.WordTrace]
  refine ⟨10523020227133538055925787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112245549089424405929875061 10523020227133538055925787)
  ·
    refine ⟨15784530340700307083888681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10523020227133538055925787 15784530340700307083888681)
    ·
      refine ⟨11838397755525230312916511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15784530340700307083888681 11838397755525230312916511)
      ·
        refine ⟨17757596633287845469374767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11838397755525230312916511 17757596633287845469374767)
        ·
          refine ⟨26636394949931768204062151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17757596633287845469374767 26636394949931768204062151)
          ·
            refine ⟨39954592424897652306093227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26636394949931768204062151 39954592424897652306093227)
            ·
              refine ⟨59931888637346478459139841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39954592424897652306093227 59931888637346478459139841)
              ·
                refine ⟨44948916478009858844354881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59931888637346478459139841 44948916478009858844354881)
                ·
                  refine ⟨33711687358507394133266161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44948916478009858844354881 33711687358507394133266161)
                  ·
                    refine ⟨25283765518880545599949621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33711687358507394133266161 25283765518880545599949621)
                    ·
                      refine ⟨2370353017395051149995277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25283765518880545599949621 2370353017395051149995277)
                      ·
                        rfl

theorem cell23_4616246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_4616246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616246 prefixEnd_4616246 := by exact prefixLift 4616246
  have htrace : WordTrace (prefixWord ++ tailWord_4616246) baseStart_4616246 baseEnd_4616246 := by
    simpa [prefixWord, tailWord_4616246, baseEnd_4616246] using wordTrace_append hprefix tailTrace_4616246
  have hstable : (prefixWord ++ tailWord_4616246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616246).length < 2 ^ (prefixWord ++ tailWord_4616246).sum := by decide
  have hdescent : baseEnd_4616246 < baseStart_4616246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616279 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 7]
def baseStart_4616279 : Nat := 118140960795 + 4616279 * 2 ^ 59
def prefixEnd_4616279 : Nat := 4983230072969 + 3 ^ 40 * 4616279 * 2
def baseEnd_4616279 : Nat := 263374440250738835653625

theorem tailTrace_4616279 : CollatzResearch.WordTrace tailWord_4616279 prefixEnd_4616279 263374440250738835653625 := by
  unfold tailWord_4616279
  simp only [CollatzResearch.WordTrace]
  refine ⟨168369527243017055530763891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112246351495344703687175927 168369527243017055530763891)
  ·
    refine ⟨252554290864525583296145837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168369527243017055530763891 252554290864525583296145837)
    ·
      refine ⟨94707859074197093736054689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252554290864525583296145837 94707859074197093736054689)
      ·
        refine ⟨71030894305647820302041017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94707859074197093736054689 71030894305647820302041017)
        ·
          refine ⟨53273170729235865226530763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71030894305647820302041017 53273170729235865226530763)
          ·
            refine ⟨79909756093853797839796145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53273170729235865226530763 79909756093853797839796145)
            ·
              refine ⟨59932317070390348379847109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79909756093853797839796145 59932317070390348379847109)
              ·
                refine ⟨11237309450698190321221333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59932317070390348379847109 11237309450698190321221333)
                ·
                  refine ⟨263374440250738835653625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11237309450698190321221333 263374440250738835653625)
                  ·
                    rfl

theorem cell23_4616279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 7].length) (baseStart_4616279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616279 prefixEnd_4616279 := by exact prefixLift 4616279
  have htrace : WordTrace (prefixWord ++ tailWord_4616279) baseStart_4616279 baseEnd_4616279 := by
    simpa [prefixWord, tailWord_4616279, baseEnd_4616279] using wordTrace_append hprefix tailTrace_4616279
  have hstable : (prefixWord ++ tailWord_4616279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616279).length < 2 ^ (prefixWord ++ tailWord_4616279).sum := by decide
  have hdescent : baseEnd_4616279 < baseStart_4616279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616313 : List Nat := [1, 2, 1, 3, 4, 2, 1, 4, 5]
def baseStart_4616313 : Nat := 118140960795 + 4616313 * 2 ^ 59
def prefixEnd_4616313 : Nat := 4983230072969 + 3 ^ 40 * 4616313 * 2
def baseEnd_4616313 : Nat := 263376380066544709761941

theorem tailTrace_4616313 : CollatzResearch.WordTrace tailWord_4616313 prefixEnd_4616313 263376380066544709761941 := by
  unfold tailWord_4616313
  simp only [CollatzResearch.WordTrace]
  refine ⟨168370767324893879337501593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112247178216595919558334395 168370767324893879337501593)
  ·
    refine ⟨126278075493670409503126195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168370767324893879337501593 126278075493670409503126195)
    ·
      refine ⟨189417113240505614254689293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126278075493670409503126195 189417113240505614254689293)
      ·
        refine ⟨71031417465189605345508485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189417113240505614254689293 71031417465189605345508485)
        ·
          refine ⟨13318390774723051002282841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71031417465189605345508485 13318390774723051002282841)
          ·
            refine ⟨9988793081042288251712131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13318390774723051002282841 9988793081042288251712131)
            ·
              refine ⟨14983189621563432377568197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9988793081042288251712131 14983189621563432377568197)
              ·
                refine ⟨2809348054043143570794037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14983189621563432377568197 2809348054043143570794037)
                ·
                  refine ⟨263376380066544709761941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2809348054043143570794037 263376380066544709761941)
                  ·
                    rfl

theorem cell23_4616313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 5].length) (baseStart_4616313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616313 prefixEnd_4616313 := by exact prefixLift 4616313
  have htrace : WordTrace (prefixWord ++ tailWord_4616313) baseStart_4616313 baseEnd_4616313 := by
    simpa [prefixWord, tailWord_4616313, baseEnd_4616313] using wordTrace_append hprefix tailTrace_4616313
  have hstable : (prefixWord ++ tailWord_4616313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616313).length < 2 ^ (prefixWord ++ tailWord_4616313).sum := by decide
  have hdescent : baseEnd_4616313 < baseStart_4616313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616450 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_4616450 : Nat := 118140960795 + 4616450 * 2 ^ 59
def prefixEnd_4616450 : Nat := 4983230072969 + 3 ^ 40 * 4616450 * 2
def baseEnd_4616450 : Nat := 790152589149522783948113

theorem tailTrace_4616450 : CollatzResearch.WordTrace tailWord_4616450 prefixEnd_4616450 790152589149522783948113 := by
  unfold tailWord_4616450
  simp only [CollatzResearch.WordTrace]
  refine ⟨42093941031349387933809701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112250509416931701156825869 42093941031349387933809701)
  ·
    refine ⟨7892613943378010237589319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42093941031349387933809701 7892613943378010237589319)
    ·
      refine ⟨11838920915067015356383979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7892613943378010237589319 11838920915067015356383979)
      ·
        refine ⟨17758381372600523034575969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11838920915067015356383979 17758381372600523034575969)
        ·
          refine ⟨13318786029450392275931977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17758381372600523034575969 13318786029450392275931977)
          ·
            refine ⟨9989089522087794206948983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13318786029450392275931977 9989089522087794206948983)
            ·
              refine ⟨14983634283131691310423475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9989089522087794206948983 14983634283131691310423475)
              ·
                refine ⟨22475451424697536965635213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14983634283131691310423475 22475451424697536965635213)
                ·
                  refine ⟨8428294284261576362113205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22475451424697536965635213 8428294284261576362113205)
                  ·
                    refine ⟨790152589149522783948113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8428294284261576362113205 790152589149522783948113)
                    ·
                      rfl

theorem cell23_4616450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_4616450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616450 prefixEnd_4616450 := by exact prefixLift 4616450
  have htrace : WordTrace (prefixWord ++ tailWord_4616450) baseStart_4616450 baseEnd_4616450 := by
    simpa [prefixWord, tailWord_4616450, baseEnd_4616450] using wordTrace_append hprefix tailTrace_4616450
  have hstable : (prefixWord ++ tailWord_4616450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616450).length < 2 ^ (prefixWord ++ tailWord_4616450).sum := by decide
  have hdescent : baseEnd_4616450 < baseStart_4616450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616453 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 4]
def baseStart_4616453 : Nat := 118140960795 + 4616453 * 2 ^ 59
def prefixEnd_4616453 : Nat := 4983230072969 + 3 ^ 40 * 4616453 * 2
def baseEnd_4616453 : Nat := 2370459307890531840106825

theorem tailTrace_4616453 : CollatzResearch.WordTrace tailWord_4616453 prefixEnd_4616453 2370459307890531840106825 := by
  unfold tailWord_4616453
  simp only [CollatzResearch.WordTrace]
  refine ⟨168375873544386683247598013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112250582362924455498398675 168375873544386683247598013)
  ·
    refine ⟨63140952579145006217849255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168375873544386683247598013 63140952579145006217849255)
    ·
      refine ⟨94711428868717509326773883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63140952579145006217849255 94711428868717509326773883)
      ·
        refine ⟨142067143303076263990160825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94711428868717509326773883 142067143303076263990160825)
        ·
          refine ⟨106550357477307197992620619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142067143303076263990160825 106550357477307197992620619)
          ·
            refine ⟨159825536215960796988930929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106550357477307197992620619 159825536215960796988930929)
            ·
              refine ⟨119869152161970597741698197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159825536215960796988930929 119869152161970597741698197)
              ·
                refine ⟨5618866507592371769142103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119869152161970597741698197 5618866507592371769142103)
                ·
                  refine ⟨8428299761388557653713155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5618866507592371769142103 8428299761388557653713155)
                  ·
                    refine ⟨12642449642082836480569733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8428299761388557653713155 12642449642082836480569733)
                    ·
                      refine ⟨2370459307890531840106825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12642449642082836480569733 2370459307890531840106825)
                      ·
                        rfl

theorem cell23_4616453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_4616453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616453 prefixEnd_4616453 := by exact prefixLift 4616453
  have htrace : WordTrace (prefixWord ++ tailWord_4616453) baseStart_4616453 baseEnd_4616453 := by
    simpa [prefixWord, tailWord_4616453, baseEnd_4616453] using wordTrace_append hprefix tailTrace_4616453
  have hstable : (prefixWord ++ tailWord_4616453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616453).length < 2 ^ (prefixWord ++ tailWord_4616453).sum := by decide
  have hdescent : baseEnd_4616453 < baseStart_4616453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616480 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 2, 4]
def baseStart_4616480 : Nat := 118140960795 + 4616480 * 2 ^ 59
def prefixEnd_4616480 : Nat := 4983230072969 + 3 ^ 40 * 4616480 * 2
def baseEnd_4616480 : Nat := 790157723956067744823067

theorem tailTrace_4616480 : CollatzResearch.WordTrace tailWord_4616480 prefixEnd_4616480 790157723956067744823067 := by
  unfold tailWord_4616480
  simp only [CollatzResearch.WordTrace]
  refine ⟨84188429157644433429415447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112251238876859244572553929 84188429157644433429415447)
  ·
    refine ⟨126282643736466650144123171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84188429157644433429415447 126282643736466650144123171)
    ·
      refine ⟨189423965604699975216184757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126282643736466650144123171 189423965604699975216184757)
      ·
        refine ⟨17758496775440622676517321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189423965604699975216184757 17758496775440622676517321)
        ·
          refine ⟨13318872581580467007387991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17758496775440622676517321 13318872581580467007387991)
          ·
            refine ⟨19978308872370700511081987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13318872581580467007387991 19978308872370700511081987)
            ·
              refine ⟨29967463308556050766622981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19978308872370700511081987 29967463308556050766622981)
              ·
                refine ⟨5618899370354259518741809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29967463308556050766622981 5618899370354259518741809)
                ·
                  refine ⟨4214174527765694639056357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5618899370354259518741809 4214174527765694639056357)
                  ·
                    refine ⟨790157723956067744823067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4214174527765694639056357 790157723956067744823067)
                    ·
                      rfl

theorem cell23_4616480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2, 4].length) (baseStart_4616480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616480 prefixEnd_4616480 := by exact prefixLift 4616480
  have htrace : WordTrace (prefixWord ++ tailWord_4616480) baseStart_4616480 baseEnd_4616480 := by
    simpa [prefixWord, tailWord_4616480, baseEnd_4616480] using wordTrace_append hprefix tailTrace_4616480
  have hstable : (prefixWord ++ tailWord_4616480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616480).length < 2 ^ (prefixWord ++ tailWord_4616480).sum := by decide
  have hdescent : baseEnd_4616480 < baseStart_4616480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616500 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_4616500 : Nat := 118140960795 + 4616500 * 2 ^ 59
def prefixEnd_4616500 : Nat := 4983230072969 + 3 ^ 40 * 4616500 * 2
def baseEnd_4616500 : Nat := 2370483441481293156219109

theorem tailTrace_4616500 : CollatzResearch.WordTrace tailWord_4616500 prefixEnd_4616500 2370483441481293156219109 := by
  unfold tailWord_4616500
  simp only [CollatzResearch.WordTrace]
  refine ⟨84188793887608205137279477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112251725183477606849705969 84188793887608205137279477)
  ·
    refine ⟨7892699426963269231619951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84188793887608205137279477 7892699426963269231619951)
    ·
      refine ⟨11839049140444903847429927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7892699426963269231619951 11839049140444903847429927)
      ·
        refine ⟨17758573710667355771144891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11839049140444903847429927 17758573710667355771144891)
        ·
          refine ⟨26637860566001033656717337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17758573710667355771144891 26637860566001033656717337)
          ·
            refine ⟨19978395424500775242538003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26637860566001033656717337 19978395424500775242538003)
            ·
              refine ⟨29967593136751162863807005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19978395424500775242538003 29967593136751162863807005)
              ·
                refine ⟨11237847426281686073927627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29967593136751162863807005 11237847426281686073927627)
                ·
                  refine ⟨16856771139422529110891441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11237847426281686073927627 16856771139422529110891441)
                  ·
                    refine ⟨12642578354566896833168581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16856771139422529110891441 12642578354566896833168581)
                    ·
                      refine ⟨2370483441481293156219109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12642578354566896833168581 2370483441481293156219109)
                      ·
                        rfl

theorem cell23_4616500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_4616500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616500 prefixEnd_4616500 := by exact prefixLift 4616500
  have htrace : WordTrace (prefixWord ++ tailWord_4616500) baseStart_4616500 baseEnd_4616500 := by
    simpa [prefixWord, tailWord_4616500, baseEnd_4616500] using wordTrace_append hprefix tailTrace_4616500
  have hstable : (prefixWord ++ tailWord_4616500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616500).length < 2 ^ (prefixWord ++ tailWord_4616500).sum := by decide
  have hdescent : baseEnd_4616500 < baseStart_4616500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616510 : List Nat := [4, 2, 1, 2, 1, 3, 3, 7]
def baseStart_4616510 : Nat := 118140960795 + 4616510 * 2 ^ 59
def prefixEnd_4616510 : Nat := 4983230072969 + 3 ^ 40 * 4616510 * 2
def baseEnd_4616510 : Nat := 87795873195845856188669

theorem tailTrace_4616510 : CollatzResearch.WordTrace tailWord_4616510 prefixEnd_4616510 87795873195845856188669 := by
  unfold tailWord_4616510
  simp only [CollatzResearch.WordTrace]
  refine ⟨21047244063147522747802873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112251968336786787988281989 21047244063147522747802873)
  ·
    refine ⟨15785433047360642060852155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21047244063147522747802873 15785433047360642060852155)
    ·
      refine ⟨23678149571040963091278233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15785433047360642060852155 23678149571040963091278233)
      ·
        refine ⟨17758612178280722318458675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23678149571040963091278233 17758612178280722318458675)
        ·
          refine ⟨26637918267421083477688013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17758612178280722318458675 26637918267421083477688013)
          ·
            refine ⟨9989219350282906304133005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26637918267421083477688013 9989219350282906304133005)
            ·
              refine ⟨3745957256356089864049877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9989219350282906304133005 3745957256356089864049877)
              ·
                refine ⟨87795873195845856188669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3745957256356089864049877 87795873195845856188669)
                ·
                  rfl

theorem cell23_4616510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_4616510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616510 prefixEnd_4616510 := by exact prefixLift 4616510
  have htrace : WordTrace (prefixWord ++ tailWord_4616510) baseStart_4616510 baseEnd_4616510 := by
    simpa [prefixWord, tailWord_4616510, baseEnd_4616510] using wordTrace_append hprefix tailTrace_4616510
  have hstable : (prefixWord ++ tailWord_4616510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616510).length < 2 ^ (prefixWord ++ tailWord_4616510).sum := by decide
  have hdescent : baseEnd_4616510 < baseStart_4616510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616600 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 7]
def baseStart_4616600 : Nat := 118140960795 + 4616600 * 2 ^ 59
def prefixEnd_4616600 : Nat := 4983230072969 + 3 ^ 40 * 4616600 * 2
def baseEnd_4616600 : Nat := 263392754394082529440961

theorem tailTrace_4616600 : CollatzResearch.WordTrace tailWord_4616600 prefixEnd_4616600 263392754394082529440961 := by
  unfold tailWord_4616600
  simp only [CollatzResearch.WordTrace]
  refine ⟨84190617537427063676599627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112254156716569418235466169 84190617537427063676599627)
  ·
    refine ⟨126285926306140595514899441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84190617537427063676599627 126285926306140595514899441)
    ·
      refine ⟨94714444729605446636174581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126285926306140595514899441 94714444729605446636174581)
      ·
        refine ⟨8879479193400510622141367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94714444729605446636174581 8879479193400510622141367)
        ·
          refine ⟨13319218790100765933212051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8879479193400510622141367 13319218790100765933212051)
          ·
            refine ⟨19978828185151148899818077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13319218790100765933212051 19978828185151148899818077)
            ·
              refine ⟨7492060569431680837431779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19978828185151148899818077 7492060569431680837431779)
              ·
                refine ⟨11238090854147521256147669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7492060569431680837431779 11238090854147521256147669)
                ·
                  refine ⟨263392754394082529440961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11238090854147521256147669 263392754394082529440961)
                  ·
                    rfl

theorem cell23_4616600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 7].length) (baseStart_4616600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616600 prefixEnd_4616600 := by exact prefixLift 4616600
  have htrace : WordTrace (prefixWord ++ tailWord_4616600) baseStart_4616600 baseEnd_4616600 := by
    simpa [prefixWord, tailWord_4616600, baseEnd_4616600] using wordTrace_append hprefix tailTrace_4616600
  have hstable : (prefixWord ++ tailWord_4616600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616600).length < 2 ^ (prefixWord ++ tailWord_4616600).sum := by decide
  have hdescent : baseEnd_4616600 < baseStart_4616600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616610 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_4616610 : Nat := 118140960795 + 4616610 * 2 ^ 59
def prefixEnd_4616610 : Nat := 4983230072969 + 3 ^ 40 * 4616610 * 2
def baseEnd_4616610 : Nat := 2370539924353287725843603

theorem tailTrace_4616610 : CollatzResearch.WordTrace tailWord_4616610 prefixEnd_4616610 2370539924353287725843603 := by
  unfold tailWord_4616610
  simp only [CollatzResearch.WordTrace]
  refine ⟨42095399951204474765265821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112254399869878599374042189 42095399951204474765265821)
  ·
    refine ⟨15785774981701678036974683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42095399951204474765265821 15785774981701678036974683)
    ·
      refine ⟨23678662472552517055462025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15785774981701678036974683 23678662472552517055462025)
      ·
        refine ⟨17758996854414387791596519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23678662472552517055462025 17758996854414387791596519)
        ·
          refine ⟨26638495281621581687394779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17758996854414387791596519 26638495281621581687394779)
          ·
            refine ⟨39957742922432372531092169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26638495281621581687394779 39957742922432372531092169)
            ·
              refine ⟨29968307191824279398319127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39957742922432372531092169 29968307191824279398319127)
              ·
                refine ⟨44952460787736419097478691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29968307191824279398319127 44952460787736419097478691)
                ·
                  refine ⟨67428691181604628646218037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44952460787736419097478691 67428691181604628646218037)
                  ·
                    refine ⟨6321439798275433935582941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67428691181604628646218037 6321439798275433935582941)
                    ·
                      refine ⟨2370539924353287725843603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6321439798275433935582941 2370539924353287725843603)
                      ·
                        rfl

theorem cell23_4616610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_4616610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616610 prefixEnd_4616610 := by exact prefixLift 4616610
  have htrace : WordTrace (prefixWord ++ tailWord_4616610) baseStart_4616610 baseEnd_4616610 := by
    simpa [prefixWord, tailWord_4616610, baseEnd_4616610] using wordTrace_append hprefix tailTrace_4616610
  have hstable : (prefixWord ++ tailWord_4616610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616610).length < 2 ^ (prefixWord ++ tailWord_4616610).sum := by decide
  have hdescent : baseEnd_4616610 < baseStart_4616610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616611 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 2, 2, 2]
def baseStart_4616611 : Nat := 118140960795 + 4616611 * 2 ^ 59
def prefixEnd_4616611 : Nat := 4983230072969 + 3 ^ 40 * 4616611 * 2
def baseEnd_4616611 : Nat := 2370540437833942221931099

theorem tailTrace_4616611 : CollatzResearch.WordTrace tailWord_4616611 prefixEnd_4616611 2370540437833942221931099 := by
  unfold tailWord_4616611
  simp only [CollatzResearch.WordTrace]
  refine ⟨168381636277814276231849687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112254424185209517487899791 168381636277814276231849687)
  ·
    refine ⟨252572454416721414347774531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168381636277814276231849687 252572454416721414347774531)
    ·
      refine ⟨378858681625082121521661797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252572454416721414347774531 378858681625082121521661797)
      ·
        refine ⟨71036002804702897785311587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 378858681625082121521661797 71036002804702897785311587)
        ·
          refine ⟨106554004207054346677967381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71036002804702897785311587 106554004207054346677967381)
          ·
            refine ⟨4994718947205672500529721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106554004207054346677967381 4994718947205672500529721)
            ·
              refine ⟨3746039210404254375397291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4994718947205672500529721 3746039210404254375397291)
              ·
                refine ⟨5619058815606381563095937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3746039210404254375397291 5619058815606381563095937)
                ·
                  refine ⟨4214294111704786172321953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5619058815606381563095937 4214294111704786172321953)
                  ·
                    refine ⟨3160720583778589629241465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4214294111704786172321953 3160720583778589629241465)
                    ·
                      refine ⟨2370540437833942221931099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160720583778589629241465 2370540437833942221931099)
                      ·
                        rfl

theorem cell23_4616611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_4616611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616611 prefixEnd_4616611 := by exact prefixLift 4616611
  have htrace : WordTrace (prefixWord ++ tailWord_4616611) baseStart_4616611 baseEnd_4616611 := by
    simpa [prefixWord, tailWord_4616611, baseEnd_4616611] using wordTrace_append hprefix tailTrace_4616611
  have hstable : (prefixWord ++ tailWord_4616611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616611).length < 2 ^ (prefixWord ++ tailWord_4616611).sum := by decide
  have hdescent : baseEnd_4616611 < baseStart_4616611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616613 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_4616613 : Nat := 118140960795 + 4616613 * 2 ^ 59
def prefixEnd_4616613 : Nat := 4983230072969 + 3 ^ 40 * 4616613 * 2
def baseEnd_4616613 : Nat := 790180488265083738035363

theorem tailTrace_4616613 : CollatzResearch.WordTrace tailWord_4616613 prefixEnd_4616613 790180488265083738035363 := by
  unfold tailWord_4616613
  simp only [CollatzResearch.WordTrace]
  refine ⟨168381709223807030573422493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112254472815871353715614995 168381709223807030573422493)
  ·
    refine ⟨63143140958927636465033435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168381709223807030573422493 63143140958927636465033435)
    ·
      refine ⟨94714711438391454697550153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63143140958927636465033435 94714711438391454697550153)
      ·
        refine ⟨71036033578793591023162615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94714711438391454697550153 71036033578793591023162615)
        ·
          refine ⟨106554050368190386534743923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71036033578793591023162615 106554050368190386534743923)
          ·
            refine ⟨159831075552285579802115885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106554050368190386534743923 159831075552285579802115885)
            ·
              refine ⟨59936653332107092425793457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159831075552285579802115885 59936653332107092425793457)
              ·
                refine ⟨44952489999080319319345093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59936653332107092425793457 44952489999080319319345093)
                ·
                  refine ⟨8428591874827559872377205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44952489999080319319345093 8428591874827559872377205)
                  ·
                    refine ⟨790180488265083738035363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8428591874827559872377205 790180488265083738035363)
                    ·
                      rfl

theorem cell23_4616613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_4616613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616613 prefixEnd_4616613 := by exact prefixLift 4616613
  have htrace : WordTrace (prefixWord ++ tailWord_4616613) baseStart_4616613 baseEnd_4616613 := by
    simpa [prefixWord, tailWord_4616613, baseEnd_4616613] using wordTrace_append hprefix tailTrace_4616613
  have hstable : (prefixWord ++ tailWord_4616613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616613).length < 2 ^ (prefixWord ++ tailWord_4616613).sum := by decide
  have hdescent : baseEnd_4616613 < baseStart_4616613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616650 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_4616650 : Nat := 118140960795 + 4616650 * 2 ^ 59
def prefixEnd_4616650 : Nat := 4983230072969 + 3 ^ 40 * 4616650 * 2
def baseEnd_4616650 : Nat := 2370560463579467569343419

theorem tailTrace_4616650 : CollatzResearch.WordTrace tailWord_4616650 prefixEnd_4616650 2370560463579467569343419 := by
  unfold tailWord_4616650
  simp only [CollatzResearch.WordTrace]
  refine ⟨42095764681168246473129851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112255372483115323928346269 42095764681168246473129851)
  ·
    refine ⟨63143647021752369709694777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42095764681168246473129851 63143647021752369709694777)
    ·
      refine ⟨47357735266314277282271083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63143647021752369709694777 47357735266314277282271083)
      ·
        refine ⟨71036602899471415923406625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47357735266314277282271083 71036602899471415923406625)
        ·
          refine ⟨53277452174603561942554969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71036602899471415923406625 53277452174603561942554969)
          ·
            refine ⟨39958089130952671456916227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53277452174603561942554969 39958089130952671456916227)
            ·
              refine ⟨59937133696429007185374341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39958089130952671456916227 59937133696429007185374341)
              ·
                refine ⟨11238212568080438847257689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59937133696429007185374341 11238212568080438847257689)
                ·
                  refine ⟨8428659426060329135443267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11238212568080438847257689 8428659426060329135443267)
                  ·
                    refine ⟨12642989139090493703164901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8428659426060329135443267 12642989139090493703164901)
                    ·
                      refine ⟨2370560463579467569343419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12642989139090493703164901 2370560463579467569343419)
                      ·
                        rfl

theorem cell23_4616650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_4616650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616650 prefixEnd_4616650 := by exact prefixLift 4616650
  have htrace : WordTrace (prefixWord ++ tailWord_4616650) baseStart_4616650 baseEnd_4616650 := by
    simpa [prefixWord, tailWord_4616650, baseEnd_4616650] using wordTrace_append hprefix tailTrace_4616650
  have hstable : (prefixWord ++ tailWord_4616650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616650).length < 2 ^ (prefixWord ++ tailWord_4616650).sum := by decide
  have hdescent : baseEnd_4616650 < baseStart_4616650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616663 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_4616663 : Nat := 118140960795 + 4616663 * 2 ^ 59
def prefixEnd_4616663 : Nat := 4983230072969 + 3 ^ 40 * 4616663 * 2
def baseEnd_4616663 : Nat := 2370567138827976018480859

theorem tailTrace_4616663 : CollatzResearch.WordTrace tailWord_4616663 prefixEnd_4616663 2370567138827976018480859 := by
  unfold tailWord_4616663
  simp only [CollatzResearch.WordTrace]
  refine ⟨168383532873625889112742643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112255688582417259408495095 168383532873625889112742643)
  ·
    refine ⟨252575299310438833669113965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168383532873625889112742643 252575299310438833669113965)
    ·
      refine ⟨94715737241414562625917737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252575299310438833669113965 94715737241414562625917737)
      ·
        refine ⟨71036802931060921969438303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94715737241414562625917737 71036802931060921969438303)
        ·
          refine ⟨106555204396591382954157455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71036802931060921969438303 106555204396591382954157455)
          ·
            refine ⟨159832806594887074431236183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106555204396591382954157455 159832806594887074431236183)
            ·
              refine ⟨239749209892330611646854275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159832806594887074431236183 239749209892330611646854275)
              ·
                refine ⟨359623814838495917470281413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239749209892330611646854275 359623814838495917470281413)
                ·
                  refine ⟨67429465282217984525677765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 359623814838495917470281413 67429465282217984525677765)
                  ·
                    refine ⟨12643024740415872098564581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67429465282217984525677765 12643024740415872098564581)
                    ·
                      refine ⟨2370567138827976018480859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12643024740415872098564581 2370567138827976018480859)
                      ·
                        rfl

theorem cell23_4616663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_4616663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616663 prefixEnd_4616663 := by exact prefixLift 4616663
  have htrace : WordTrace (prefixWord ++ tailWord_4616663) baseStart_4616663 baseEnd_4616663 := by
    simpa [prefixWord, tailWord_4616663, baseEnd_4616663] using wordTrace_append hprefix tailTrace_4616663
  have hstable : (prefixWord ++ tailWord_4616663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616663).length < 2 ^ (prefixWord ++ tailWord_4616663).sum := by decide
  have hdescent : baseEnd_4616663 < baseStart_4616663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616713 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_4616713 : Nat := 118140960795 + 4616713 * 2 ^ 59
def prefixEnd_4616713 : Nat := 4983230072969 + 3 ^ 40 * 4616713 * 2
def baseEnd_4616713 : Nat := 2370592812860700822855629

theorem tailTrace_4616713 : CollatzResearch.WordTrace tailWord_4616713 prefixEnd_4616713 2370592812860700822855629 := by
  unfold tailWord_4616713
  simp only [CollatzResearch.WordTrace]
  refine ⟨168385356523444747652062793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112256904348963165101375195 168385356523444747652062793)
  ·
    refine ⟨126289017392583560739047095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168385356523444747652062793 126289017392583560739047095)
    ·
      refine ⟨189433526088875341108570643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126289017392583560739047095 189433526088875341108570643)
      ·
        refine ⟨284150289133313011662855965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189433526088875341108570643 284150289133313011662855965)
        ·
          refine ⟨106556358424992379373570987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284150289133313011662855965 106556358424992379373570987)
          ·
            refine ⟨159834537637488569060356481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106556358424992379373570987 159834537637488569060356481)
            ·
              refine ⟨119875903228116426795267361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159834537637488569060356481 119875903228116426795267361)
              ·
                refine ⟨89906927421087320096450521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119875903228116426795267361 89906927421087320096450521)
                ·
                  refine ⟨67430195565815490072337891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89906927421087320096450521 67430195565815490072337891)
                  ·
                    refine ⟨101145293348723235108506837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67430195565815490072337891 101145293348723235108506837)
                    ·
                      refine ⟨2370592812860700822855629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101145293348723235108506837 2370592812860700822855629)
                      ·
                        rfl

theorem cell23_4616713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_4616713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616713 prefixEnd_4616713 := by exact prefixLift 4616713
  have htrace : WordTrace (prefixWord ++ tailWord_4616713) baseStart_4616713 baseEnd_4616713 := by
    simpa [prefixWord, tailWord_4616713, baseEnd_4616713] using wordTrace_append hprefix tailTrace_4616713
  have hstable : (prefixWord ++ tailWord_4616713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616713).length < 2 ^ (prefixWord ++ tailWord_4616713).sum := by decide
  have hdescent : baseEnd_4616713 < baseStart_4616713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616737 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 1, 5]
def baseStart_4616737 : Nat := 118140960795 + 4616737 * 2 ^ 59
def prefixEnd_4616737 : Nat := 4983230072969 + 3 ^ 40 * 4616737 * 2
def baseEnd_4616737 : Nat := 790201712132136242985173

theorem tailTrace_4616737 : CollatzResearch.WordTrace tailWord_4616737 prefixEnd_4616737 790201712132136242985173 := by
  unfold tailWord_4616737
  simp only [CollatzResearch.WordTrace]
  refine ⟨168386231875357799750936465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112257487916905199833957643 168386231875357799750936465)
  ·
    refine ⟨126289673906518349813202349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168386231875357799750936465 126289673906518349813202349)
    ·
      refine ⟨47358627714944381179950881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126289673906518349813202349 47358627714944381179950881)
      ·
        refine ⟨35518970786208285884963161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47358627714944381179950881 35518970786208285884963161)
        ·
          refine ⟨26639228089656214413722371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35518970786208285884963161 26639228089656214413722371)
          ·
            refine ⟨39958842134484321620583557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26639228089656214413722371 39958842134484321620583557)
            ·
              refine ⟨7492282900215810303859417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39958842134484321620583557 7492282900215810303859417)
              ·
                refine ⟨5619212175161857727894563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7492282900215810303859417 5619212175161857727894563)
                ·
                  refine ⟨8428818262742786591841845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5619212175161857727894563 8428818262742786591841845)
                  ·
                    refine ⟨790201712132136242985173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8428818262742786591841845 790201712132136242985173)
                    ·
                      rfl

theorem cell23_4616737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_4616737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616737 prefixEnd_4616737 := by exact prefixLift 4616737
  have htrace : WordTrace (prefixWord ++ tailWord_4616737) baseStart_4616737 baseEnd_4616737 := by
    simpa [prefixWord, tailWord_4616737, baseEnd_4616737] using wordTrace_append hprefix tailTrace_4616737
  have hstable : (prefixWord ++ tailWord_4616737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616737).length < 2 ^ (prefixWord ++ tailWord_4616737).sum := by decide
  have hdescent : baseEnd_4616737 < baseStart_4616737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616744 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4616744 : Nat := 118140960795 + 4616744 * 2 ^ 59
def prefixEnd_4616744 : Nat := 4983230072969 + 3 ^ 40 * 4616744 * 2
def baseEnd_4616744 : Nat := 2370608730760990201567987

theorem tailTrace_4616744 : CollatzResearch.WordTrace tailWord_4616744 prefixEnd_4616744 2370608730760990201567987 := by
  unfold tailWord_4616744
  simp only [CollatzResearch.WordTrace]
  refine ⟨84193243593166219973220643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112257658124221626630960857 84193243593166219973220643)
  ·
    refine ⟨126289865389749329959830965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84193243593166219973220643 126289865389749329959830965)
    ·
      refine ⟨11839674880288999683734153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126289865389749329959830965 11839674880288999683734153)
      ·
        refine ⟨8879756160216749762800615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11839674880288999683734153 8879756160216749762800615)
        ·
          refine ⟨13319634240325124644200923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8879756160216749762800615 13319634240325124644200923)
          ·
            refine ⟨19979451360487686966301385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13319634240325124644200923 19979451360487686966301385)
            ·
              refine ⟨14984588520365765224726039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19979451360487686966301385 14984588520365765224726039)
              ·
                refine ⟨22476882780548647837089059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14984588520365765224726039 22476882780548647837089059)
                ·
                  refine ⟨33715324170822971755633589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22476882780548647837089059 33715324170822971755633589)
                  ·
                    refine ⟨3160811641014653602090649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33715324170822971755633589 3160811641014653602090649)
                    ·
                      refine ⟨2370608730760990201567987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160811641014653602090649 2370608730760990201567987)
                      ·
                        rfl

theorem cell23_4616744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4616744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616744 prefixEnd_4616744 := by exact prefixLift 4616744
  have htrace : WordTrace (prefixWord ++ tailWord_4616744) baseStart_4616744 baseEnd_4616744 := by
    simpa [prefixWord, tailWord_4616744, baseEnd_4616744] using wordTrace_append hprefix tailTrace_4616744
  have hstable : (prefixWord ++ tailWord_4616744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616744).length < 2 ^ (prefixWord ++ tailWord_4616744).sum := by decide
  have hdescent : baseEnd_4616744 < baseStart_4616744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616757 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_4616757 : Nat := 118140960795 + 4616757 * 2 ^ 59
def prefixEnd_4616757 : Nat := 4983230072969 + 3 ^ 40 * 4616757 * 2
def baseEnd_4616757 : Nat := 2370615406009498650705427

theorem tailTrace_4616757 : CollatzResearch.WordTrace tailWord_4616757 prefixEnd_4616757 2370615406009498650705427 := by
  unfold tailWord_4616757
  simp only [CollatzResearch.WordTrace]
  refine ⟨168386961335285343166664525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112257974223523562111109683 168386961335285343166664525)
  ·
    refine ⟨63145110500732003687499197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168386961335285343166664525 63145110500732003687499197)
    ·
      refine ⟨23679416437774501382812199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63145110500732003687499197 23679416437774501382812199)
      ·
        refine ⟨35519124656661752074218299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23679416437774501382812199 35519124656661752074218299)
        ·
          refine ⟨53278686984992628111327449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35519124656661752074218299 53278686984992628111327449)
          ·
            refine ⟨39959015238744471083495587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53278686984992628111327449 39959015238744471083495587)
            ·
              refine ⟨59938522858116706625243381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39959015238744471083495587 59938522858116706625243381)
              ·
                refine ⟨5619236517948441246116567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59938522858116706625243381 5619236517948441246116567)
                ·
                  refine ⟨8428854776922661869174851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5619236517948441246116567 8428854776922661869174851)
                  ·
                    refine ⟨12643282165383992803762277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8428854776922661869174851 12643282165383992803762277)
                    ·
                      refine ⟨2370615406009498650705427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12643282165383992803762277 2370615406009498650705427)
                      ·
                        rfl

theorem cell23_4616757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_4616757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616757 prefixEnd_4616757 := by exact prefixLift 4616757
  have htrace : WordTrace (prefixWord ++ tailWord_4616757) baseStart_4616757 baseEnd_4616757 := by
    simpa [prefixWord, tailWord_4616757, baseEnd_4616757] using wordTrace_append hprefix tailTrace_4616757
  have hstable : (prefixWord ++ tailWord_4616757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616757).length < 2 ^ (prefixWord ++ tailWord_4616757).sum := by decide
  have hdescent : baseEnd_4616757 < baseStart_4616757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616767 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 2, 4]
def baseStart_4616767 : Nat := 118140960795 + 4616767 * 2 ^ 59
def prefixEnd_4616767 : Nat := 4983230072969 + 3 ^ 40 * 4616767 * 2
def baseEnd_4616767 : Nat := 790206846938681203860127

theorem tailTrace_4616767 : CollatzResearch.WordTrace tailWord_4616767 prefixEnd_4616767 790206846938681203860127 := by
  unfold tailWord_4616767
  simp only [CollatzResearch.WordTrace]
  refine ⟨168387326065249114874528555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112258217376832743249685703 168387326065249114874528555)
  ·
    refine ⟨252580989097873672311792833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168387326065249114874528555 252580989097873672311792833)
    ·
      refine ⟨189435741823405254233844625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252580989097873672311792833 189435741823405254233844625)
      ·
        refine ⟨142076806367553940675383469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189435741823405254233844625 142076806367553940675383469)
        ·
          refine ⟨53278802387832727753268801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142076806367553940675383469 53278802387832727753268801)
          ·
            refine ⟨39959101790874545814951601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53278802387832727753268801 39959101790874545814951601)
            ·
              refine ⟨29969326343155909361213701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39959101790874545814951601 29969326343155909361213701)
              ·
                refine ⟨5619248689341733005227569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29969326343155909361213701 5619248689341733005227569)
                ·
                  refine ⟨4214436517006299753920677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5619248689341733005227569 4214436517006299753920677)
                  ·
                    refine ⟨790206846938681203860127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4214436517006299753920677 790206846938681203860127)
                    ·
                      rfl

theorem cell23_4616767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 4].length) (baseStart_4616767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616767 prefixEnd_4616767 := by exact prefixLift 4616767
  have htrace : WordTrace (prefixWord ++ tailWord_4616767) baseStart_4616767 baseEnd_4616767 := by
    simpa [prefixWord, tailWord_4616767, baseEnd_4616767] using wordTrace_append hprefix tailTrace_4616767
  have hstable : (prefixWord ++ tailWord_4616767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616767).length < 2 ^ (prefixWord ++ tailWord_4616767).sum := by decide
  have hdescent : baseEnd_4616767 < baseStart_4616767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616780 : List Nat := [2, 2, 1, 3, 1, 2, 4, 8]
def baseStart_4616780 : Nat := 118140960795 + 4616780 * 2 ^ 59
def prefixEnd_4616780 : Nat := 4983230072969 + 3 ^ 40 * 4616780 * 2
def baseEnd_4616780 : Nat := 87801008002390817063623

theorem tailTrace_4616780 : CollatzResearch.WordTrace tailWord_4616780 prefixEnd_4616780 87801008002390817063623 := by
  unfold tailWord_4616780
  simp only [CollatzResearch.WordTrace]
  refine ⟨84193900107101009047375897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112258533476134678729834529 84193900107101009047375897)
  ·
    refine ⟨63145425080325756785531923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84193900107101009047375897 63145425080325756785531923)
    ·
      refine ⟨94718137620488635178297885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63145425080325756785531923 94718137620488635178297885)
      ·
        refine ⟨35519301607683238191861707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94718137620488635178297885 35519301607683238191861707)
        ·
          refine ⟨53278952411524857287792561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35519301607683238191861707 53278952411524857287792561)
          ·
            refine ⟨39959214308643642965844421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53278952411524857287792561 39959214308643642965844421)
            ·
              refine ⟨7492352682870683056095829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39959214308643642965844421 7492352682870683056095829)
              ·
                refine ⟨87801008002390817063623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7492352682870683056095829 87801008002390817063623)
                ·
                  rfl

theorem cell23_4616780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 8].length) (baseStart_4616780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616780 prefixEnd_4616780 := by exact prefixLift 4616780
  have htrace : WordTrace (prefixWord ++ tailWord_4616780) baseStart_4616780 baseEnd_4616780 := by
    simpa [prefixWord, tailWord_4616780, baseEnd_4616780] using wordTrace_append hprefix tailTrace_4616780
  have hstable : (prefixWord ++ tailWord_4616780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616780).length < 2 ^ (prefixWord ++ tailWord_4616780).sum := by decide
  have hdescent : baseEnd_4616780 < baseStart_4616780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616825 : List Nat := [1, 2, 1, 3, 3, 4, 2, 2, 1, 2, 2]
def baseStart_4616825 : Nat := 118140960795 + 4616825 * 2 ^ 59
def prefixEnd_4616825 : Nat := 4983230072969 + 3 ^ 40 * 4616825 * 2
def baseEnd_4616825 : Nat := 2370650322694004384655115

theorem tailTrace_4616825 : CollatzResearch.WordTrace tailWord_4616825 prefixEnd_4616825 2370650322694004384655115 := by
  unfold tailWord_4616825
  simp only [CollatzResearch.WordTrace]
  refine ⟨168389441499038990780139929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112259627666025993853426619 168389441499038990780139929)
  ·
    refine ⟨126292081124279243085104947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168389441499038990780139929 126292081124279243085104947)
    ·
      refine ⟨189438121686418864627657421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126292081124279243085104947 189438121686418864627657421)
      ·
        refine ⟨71039295632407074235371533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189438121686418864627657421 71039295632407074235371533)
        ·
          refine ⟨26639735862152652838264325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71039295632407074235371533 26639735862152652838264325)
          ·
            refine ⟨4994950474153622407174561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26639735862152652838264325 4994950474153622407174561)
            ·
              refine ⟨3746212855615216805380921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4994950474153622407174561 3746212855615216805380921)
              ·
                refine ⟨2809659641711412604035691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3746212855615216805380921 2809659641711412604035691)
                ·
                  refine ⟨4214489462567118906053537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809659641711412604035691 4214489462567118906053537)
                  ·
                    refine ⟨3160867096925339179540153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4214489462567118906053537 3160867096925339179540153)
                    ·
                      refine ⟨2370650322694004384655115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160867096925339179540153 2370650322694004384655115)
                      ·
                        rfl

theorem cell23_4616825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_4616825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616825 prefixEnd_4616825 := by exact prefixLift 4616825
  have htrace : WordTrace (prefixWord ++ tailWord_4616825) baseStart_4616825 baseEnd_4616825 := by
    simpa [prefixWord, tailWord_4616825, baseEnd_4616825] using wordTrace_append hprefix tailTrace_4616825
  have hstable : (prefixWord ++ tailWord_4616825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616825).length < 2 ^ (prefixWord ++ tailWord_4616825).sum := by decide
  have hdescent : baseEnd_4616825 < baseStart_4616825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616847 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 5, 4, 2]
def baseStart_4616847 : Nat := 118140960795 + 4616847 * 2 ^ 59
def prefixEnd_4616847 : Nat := 4983230072969 + 3 ^ 40 * 4616847 * 2
def baseEnd_4616847 : Nat := 2370661619268403298580013

theorem tailTrace_4616847 : CollatzResearch.WordTrace tailWord_4616847 prefixEnd_4616847 2370661619268403298580013 := by
  unfold tailWord_4616847
  simp only [CollatzResearch.WordTrace]
  refine ⟨168390243904959288537440795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112260162603306192358293863 168390243904959288537440795)
  ·
    refine ⟨252585365857438932806161193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168390243904959288537440795 252585365857438932806161193)
    ·
      refine ⟨189439024393079199604620895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252585365857438932806161193 189439024393079199604620895)
      ·
        refine ⟨284158536589618799406931343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189439024393079199604620895 284158536589618799406931343)
        ·
          refine ⟨426237804884428199110397015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284158536589618799406931343 426237804884428199110397015)
          ·
            refine ⟨639356707326642298665595523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426237804884428199110397015 639356707326642298665595523)
            ·
              refine ⟨959035060989963447998393285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639356707326642298665595523 959035060989963447998393285)
              ·
                refine ⟨179819073935618146499698741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 959035060989963447998393285 179819073935618146499698741)
                ·
                  refine ⟨16858038181464201234346757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179819073935618146499698741 16858038181464201234346757)
                  ·
                    refine ⟨3160882159024537731440017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16858038181464201234346757 3160882159024537731440017)
                    ·
                      refine ⟨2370661619268403298580013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160882159024537731440017 2370661619268403298580013)
                      ·
                        rfl

theorem cell23_4616847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 4, 2].length) (baseStart_4616847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616847 prefixEnd_4616847 := by exact prefixLift 4616847
  have htrace : WordTrace (prefixWord ++ tailWord_4616847) baseStart_4616847 baseEnd_4616847 := by
    simpa [prefixWord, tailWord_4616847, baseEnd_4616847] using wordTrace_append hprefix tailTrace_4616847
  have hstable : (prefixWord ++ tailWord_4616847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616847).length < 2 ^ (prefixWord ++ tailWord_4616847).sum := by decide
  have hdescent : baseEnd_4616847 < baseStart_4616847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616902 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_4616902 : Nat := 118140960795 + 4616902 * 2 ^ 59
def prefixEnd_4616902 : Nat := 4983230072969 + 3 ^ 40 * 4616902 * 2
def baseEnd_4616902 : Nat := 2370689860704400583392261

theorem tailTrace_4616902 : CollatzResearch.WordTrace tailWord_4616902 prefixEnd_4616902 2370689860704400583392261 := by
  unfold tailWord_4616902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5262257809992501029084155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 112261499946506688620461973 5262257809992501029084155)
  ·
    refine ⟨7893386714988751543626233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5262257809992501029084155 7893386714988751543626233)
    ·
      refine ⟨5920040036241563657719675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7893386714988751543626233 5920040036241563657719675)
      ·
        refine ⟨8880060054362345486579513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5920040036241563657719675 8880060054362345486579513)
        ·
          refine ⟨6660045040771759114934635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8880060054362345486579513 6660045040771759114934635)
          ·
            refine ⟨9990067561157638672401953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6660045040771759114934635 9990067561157638672401953)
            ·
              refine ⟨7492550670868229004301465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9990067561157638672401953 7492550670868229004301465)
              ·
                refine ⟨5619413003151171753226099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7492550670868229004301465 5619413003151171753226099)
                ·
                  refine ⟨8429119504726757629839149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5619413003151171753226099 8429119504726757629839149)
                  ·
                    refine ⟨3160919814272534111189681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8429119504726757629839149 3160919814272534111189681)
                    ·
                      refine ⟨2370689860704400583392261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160919814272534111189681 2370689860704400583392261)
                      ·
                        rfl

theorem cell23_4616902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_4616902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616902 prefixEnd_4616902 := by exact prefixLift 4616902
  have htrace : WordTrace (prefixWord ++ tailWord_4616902) baseStart_4616902 baseEnd_4616902 := by
    simpa [prefixWord, tailWord_4616902, baseEnd_4616902] using wordTrace_append hprefix tailTrace_4616902
  have hstable : (prefixWord ++ tailWord_4616902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616902).length < 2 ^ (prefixWord ++ tailWord_4616902).sum := by decide
  have hdescent : baseEnd_4616902 < baseStart_4616902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616937 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 4]
def baseStart_4616937 : Nat := 118140960795 + 4616937 * 2 ^ 59
def prefixEnd_4616937 : Nat := 4983230072969 + 3 ^ 40 * 4616937 * 2
def baseEnd_4616937 : Nat := 2370707832527307946454599

theorem tailTrace_4616937 : CollatzResearch.WordTrace tailWord_4616937 prefixEnd_4616937 2370707832527307946454599 := by
  unfold tailWord_4616937
  simp only [CollatzResearch.WordTrace]
  refine ⟨168393526474633233908217065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112262350983088822605478043 168393526474633233908217065)
  ·
    refine ⟨126295144855974925431162799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168393526474633233908217065 126295144855974925431162799)
    ·
      refine ⟨189442717283962388146744199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126295144855974925431162799 189442717283962388146744199)
      ·
        refine ⟨284164075925943582220116299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189442717283962388146744199 284164075925943582220116299)
        ·
          refine ⟨426246113888915373330174449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284164075925943582220116299 426246113888915373330174449)
          ·
            refine ⟨319684585416686529997630837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426246113888915373330174449 319684585416686529997630837)
            ·
              refine ⟨29970429882814362187277891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 319684585416686529997630837 29970429882814362187277891)
              ·
                refine ⟨44955644824221543280916837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29970429882814362187277891 44955644824221543280916837)
                ·
                  refine ⟨8429183404541539365171907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44955644824221543280916837 8429183404541539365171907)
                  ·
                    refine ⟨12643775106812309047757861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8429183404541539365171907 12643775106812309047757861)
                    ·
                      refine ⟨2370707832527307946454599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12643775106812309047757861 2370707832527307946454599)
                      ·
                        rfl

theorem cell23_4616937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_4616937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616937 prefixEnd_4616937 := by exact prefixLift 4616937
  have htrace : WordTrace (prefixWord ++ tailWord_4616937) baseStart_4616937 baseEnd_4616937 := by
    simpa [prefixWord, tailWord_4616937, baseEnd_4616937] using wordTrace_append hprefix tailTrace_4616937
  have hstable : (prefixWord ++ tailWord_4616937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616937).length < 2 ^ (prefixWord ++ tailWord_4616937).sum := by decide
  have hdescent : baseEnd_4616937 < baseStart_4616937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616954 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2]
def baseStart_4616954 : Nat := 118140960795 + 4616954 * 2 ^ 59
def prefixEnd_4616954 : Nat := 4983230072969 + 3 ^ 40 * 4616954 * 2
def baseEnd_4616954 : Nat := 2370716561698434379942021

theorem tailTrace_4616954 : CollatzResearch.WordTrace tailWord_4616954 prefixEnd_4616954 2370716561698434379942021 := by
  unfold tailWord_4616954
  simp only [CollatzResearch.WordTrace]
  refine ⟨42098536628892911452896479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112262764343714430541057277 42098536628892911452896479)
  ·
    refine ⟨63147804943339367179344719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42098536628892911452896479 63147804943339367179344719)
    ·
      refine ⟨94721707415009050769017079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63147804943339367179344719 94721707415009050769017079)
      ·
        refine ⟨142082561122513576153525619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94721707415009050769017079 142082561122513576153525619)
        ·
          refine ⟨213123841683770364230288429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142082561122513576153525619 213123841683770364230288429)
          ·
            refine ⟨79921440631413886586358161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213123841683770364230288429 79921440631413886586358161)
            ·
              refine ⟨59941080473560414939768621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79921440631413886586358161 59941080473560414939768621)
              ·
                refine ⟨22477905177585155602413233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59941080473560414939768621 22477905177585155602413233)
                ·
                  refine ⟨16858428883188866701809925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22477905177585155602413233 16858428883188866701809925)
                  ·
                    refine ⟨3160955415597912506589361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16858428883188866701809925 3160955415597912506589361)
                    ·
                      refine ⟨2370716561698434379942021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160955415597912506589361 2370716561698434379942021)
                      ·
                        rfl

theorem cell23_4616954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_4616954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616954 prefixEnd_4616954 := by exact prefixLift 4616954
  have htrace : WordTrace (prefixWord ++ tailWord_4616954) baseStart_4616954 baseEnd_4616954 := by
    simpa [prefixWord, tailWord_4616954, baseEnd_4616954] using wordTrace_append hprefix tailTrace_4616954
  have hstable : (prefixWord ++ tailWord_4616954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616954).length < 2 ^ (prefixWord ++ tailWord_4616954).sum := by decide
  have hdescent : baseEnd_4616954 < baseStart_4616954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616964 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_4616964 : Nat := 118140960795 + 4616964 * 2 ^ 59
def prefixEnd_4616964 : Nat := 4983230072969 + 3 ^ 40 * 4616964 * 2
def baseEnd_4616964 : Nat := 790240565501659780272325

theorem tailTrace_4616964 : CollatzResearch.WordTrace tailWord_4616964 prefixEnd_4616964 790240565501659780272325 := by
  unfold tailWord_4616964
  simp only [CollatzResearch.WordTrace]
  refine ⟨84197255622767708759724973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112263007497023611679633297 84197255622767708759724973)
  ·
    refine ⟨31573970858537890784896865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84197255622767708759724973 31573970858537890784896865)
    ·
      refine ⟨23680478143903418088672649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31573970858537890784896865 23680478143903418088672649)
      ·
        refine ⟨17760358607927563566504487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23680478143903418088672649 17760358607927563566504487)
        ·
          refine ⟨26640537911891345349756731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17760358607927563566504487 26640537911891345349756731)
          ·
            refine ⟨39960806867837018024635097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26640537911891345349756731 39960806867837018024635097)
            ·
              refine ⟨29970605150877763518476323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39960806867837018024635097 29970605150877763518476323)
              ·
                refine ⟨44955907726316645277714485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29970605150877763518476323 44955907726316645277714485)
                ·
                  refine ⟨4214616349342185494785733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44955907726316645277714485 4214616349342185494785733)
                  ·
                    refine ⟨790240565501659780272325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4214616349342185494785733 790240565501659780272325)
                    ·
                      rfl

theorem cell23_4616964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_4616964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616964 prefixEnd_4616964 := by exact prefixLift 4616964
  have htrace : WordTrace (prefixWord ++ tailWord_4616964) baseStart_4616964 baseEnd_4616964 := by
    simpa [prefixWord, tailWord_4616964, baseEnd_4616964] using wordTrace_append hprefix tailTrace_4616964
  have hstable : (prefixWord ++ tailWord_4616964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616964).length < 2 ^ (prefixWord ++ tailWord_4616964).sum := by decide
  have hdescent : baseEnd_4616964 < baseStart_4616964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616981 : List Nat := [1, 3, 2, 1, 2, 2, 2, 5, 1, 4]
def baseStart_4616981 : Nat := 118140960795 + 4616981 * 2 ^ 59
def prefixEnd_4616981 : Nat := 4983230072969 + 3 ^ 40 * 4616981 * 2
def baseEnd_4616981 : Nat := 790243475225368591434799

theorem tailTrace_4616981 : CollatzResearch.WordTrace tailWord_4616981 prefixEnd_4616981 790243475225368591434799 := by
  unfold tailWord_4616981
  simp only [CollatzResearch.WordTrace]
  refine ⟨168395131286473829422818797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112263420857649219615212531 168395131286473829422818797)
  ·
    refine ⟨63148174232427686033557049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168395131286473829422818797 63148174232427686033557049)
    ·
      refine ⟨47361130674320764525167787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63148174232427686033557049 47361130674320764525167787)
      ·
        refine ⟨71041696011481146787751681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47361130674320764525167787 71041696011481146787751681)
        ·
          refine ⟨53281272008610860090813761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71041696011481146787751681 53281272008610860090813761)
          ·
            refine ⟨39960954006458145068110321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53281272008610860090813761 39960954006458145068110321)
            ·
              refine ⟨29970715504843608801082741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39960954006458145068110321 29970715504843608801082741)
              ·
                refine ⟨2809754578579088325101507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29970715504843608801082741 2809754578579088325101507)
                ·
                  refine ⟨4214631867868632487652261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809754578579088325101507 4214631867868632487652261)
                  ·
                    refine ⟨790243475225368591434799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4214631867868632487652261 790243475225368591434799)
                    ·
                      rfl

theorem cell23_4616981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_4616981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616981 prefixEnd_4616981 := by exact prefixLift 4616981
  have htrace : WordTrace (prefixWord ++ tailWord_4616981) baseStart_4616981 baseEnd_4616981 := by
    simpa [prefixWord, tailWord_4616981, baseEnd_4616981] using wordTrace_append hprefix tailTrace_4616981
  have hstable : (prefixWord ++ tailWord_4616981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616981).length < 2 ^ (prefixWord ++ tailWord_4616981).sum := by decide
  have hdescent : baseEnd_4616981 < baseStart_4616981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616994 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 6]
def baseStart_4616994 : Nat := 118140960795 + 4616994 * 2 ^ 59
def prefixEnd_4616994 : Nat := 4983230072969 + 3 ^ 40 * 4616994 * 2
def baseEnd_4616994 : Nat := 263415233436068247049093

theorem tailTrace_4616994 : CollatzResearch.WordTrace tailWord_4616994 prefixEnd_4616994 263415233436068247049093 := by
  unfold tailWord_4616994
  simp only [CollatzResearch.WordTrace]
  refine ⟨42098901358856683160760509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112263736956951155095361357 42098901358856683160760509)
  ·
    refine ⟨15787088009571256185285191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42098901358856683160760509 15787088009571256185285191)
    ·
      refine ⟨23680632014356884277927787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15787088009571256185285191 23680632014356884277927787)
      ·
        refine ⟨35520948021535326416891681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23680632014356884277927787 35520948021535326416891681)
        ·
          refine ⟨26640711016151494812668761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35520948021535326416891681 26640711016151494812668761)
          ·
            refine ⟨19980533262113621109501571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26640711016151494812668761 19980533262113621109501571)
            ·
              refine ⟨29970799893170431664252357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19980533262113621109501571 29970799893170431664252357)
              ·
                refine ⟨5619524979969455937047317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29970799893170431664252357 5619524979969455937047317)
                ·
                  refine ⟨263415233436068247049093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5619524979969455937047317 263415233436068247049093)
                  ·
                    rfl

theorem cell23_4616994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_4616994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616994 prefixEnd_4616994 := by exact prefixLift 4616994
  have htrace : WordTrace (prefixWord ++ tailWord_4616994) baseStart_4616994 baseEnd_4616994 := by
    simpa [prefixWord, tailWord_4616994, baseEnd_4616994] using wordTrace_append hprefix tailTrace_4616994
  have hstable : (prefixWord ++ tailWord_4616994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616994).length < 2 ^ (prefixWord ++ tailWord_4616994).sum := by decide
  have hdescent : baseEnd_4616994 < baseStart_4616994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4616997 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_4616997 : Nat := 118140960795 + 4616997 * 2 ^ 59
def prefixEnd_4616997 : Nat := 4983230072969 + 3 ^ 40 * 4616997 * 2
def baseEnd_4616997 : Nat := 2370738641366577711704323

theorem tailTrace_4616997 : CollatzResearch.WordTrace tailWord_4616997 prefixEnd_4616997 2370738641366577711704323 := by
  unfold tailWord_4616997
  simp only [CollatzResearch.WordTrace]
  refine ⟨168395714854415864155401245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112263809902943909436934163 168395714854415864155401245)
  ·
    refine ⟨63148393070405949058275467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168395714854415864155401245 63148393070405949058275467)
    ·
      refine ⟨94722589605608923587413201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63148393070405949058275467 94722589605608923587413201)
      ·
        refine ⟨71041942204206692690559901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94722589605608923587413201 71041942204206692690559901)
        ·
          refine ⟨26640728326577509758959963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71041942204206692690559901 26640728326577509758959963)
          ·
            refine ⟨39961092489866264638439945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26640728326577509758959963 39961092489866264638439945)
            ·
              refine ⟨29970819367399698478829959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39961092489866264638439945 29970819367399698478829959)
              ·
                refine ⟨44956229051099547718244939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29970819367399698478829959 44956229051099547718244939)
                ·
                  refine ⟨67434343576649321577367409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44956229051099547718244939 67434343576649321577367409)
                  ·
                    refine ⟨50575757682486991183025557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67434343576649321577367409 50575757682486991183025557)
                    ·
                      refine ⟨2370738641366577711704323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50575757682486991183025557 2370738641366577711704323)
                      ·
                        rfl

theorem cell23_4616997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_4616997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4616997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4616997 prefixEnd_4616997 := by exact prefixLift 4616997
  have htrace : WordTrace (prefixWord ++ tailWord_4616997) baseStart_4616997 baseEnd_4616997 := by
    simpa [prefixWord, tailWord_4616997, baseEnd_4616997] using wordTrace_append hprefix tailTrace_4616997
  have hstable : (prefixWord ++ tailWord_4616997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4616997).length < 2 ^ (prefixWord ++ tailWord_4616997).sum := by decide
  have hdescent : baseEnd_4616997 < baseStart_4616997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4616997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617005 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4617005 : Nat := 118140960795 + 4617005 * 2 ^ 59
def prefixEnd_4617005 : Nat := 4983230072969 + 3 ^ 40 * 4617005 * 2
def baseEnd_4617005 : Nat := 2370742749211813680404287

theorem tailTrace_4617005 : CollatzResearch.WordTrace tailWord_4617005 prefixEnd_4617005 2370742749211813680404287 := by
  unfold tailWord_4617005
  simp only [CollatzResearch.WordTrace]
  refine ⟨168396006638386881521692469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112264004425591254347794979 168396006638386881521692469)
  ·
    refine ⟨15787125622348770142658669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168396006638386881521692469 15787125622348770142658669)
    ·
      refine ⟨5920172108380788803497001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15787125622348770142658669 5920172108380788803497001)
      ·
        refine ⟨4440129081285591602622751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5920172108380788803497001 4440129081285591602622751)
        ·
          refine ⟨6660193621928387403934127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4440129081285591602622751 6660193621928387403934127)
          ·
            refine ⟨9990290432892581105901191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6660193621928387403934127 9990290432892581105901191)
            ·
              refine ⟨14985435649338871658851787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9990290432892581105901191 14985435649338871658851787)
              ·
                refine ⟨22478153474008307488277681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14985435649338871658851787 22478153474008307488277681)
                ·
                  refine ⟨16858615105506230616208261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22478153474008307488277681 16858615105506230616208261)
                  ·
                    refine ⟨3160990332282418240539049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16858615105506230616208261 3160990332282418240539049)
                    ·
                      refine ⟨2370742749211813680404287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3160990332282418240539049 2370742749211813680404287)
                      ·
                        rfl

theorem cell23_4617005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4617005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617005 prefixEnd_4617005 := by exact prefixLift 4617005
  have htrace : WordTrace (prefixWord ++ tailWord_4617005) baseStart_4617005 baseEnd_4617005 := by
    simpa [prefixWord, tailWord_4617005, baseEnd_4617005] using wordTrace_append hprefix tailTrace_4617005
  have hstable : (prefixWord ++ tailWord_4617005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617005).length < 2 ^ (prefixWord ++ tailWord_4617005).sum := by decide
  have hdescent : baseEnd_4617005 < baseStart_4617005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617025 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4617025 : Nat := 118140960795 + 4617025 * 2 ^ 59
def prefixEnd_4617025 : Nat := 4983230072969 + 3 ^ 40 * 4617025 * 2
def baseEnd_4617025 : Nat := 2370753018824903602154195

theorem tailTrace_4617025 : CollatzResearch.WordTrace tailWord_4617025 prefixEnd_4617025 2370753018824903602154195 := by
  unfold tailWord_4617025
  simp only [CollatzResearch.WordTrace]
  refine ⟨168396736098314424937420529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112264490732209616624947019 168396736098314424937420529)
  ·
    refine ⟨126297552073735818703065397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168396736098314424937420529 126297552073735818703065397)
    ·
      refine ⟨11840395506912733003412381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126297552073735818703065397 11840395506912733003412381)
      ·
        refine ⟨4440148315092274876279643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11840395506912733003412381 4440148315092274876279643)
        ·
          refine ⟨6660222472638412314419465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4440148315092274876279643 6660222472638412314419465)
          ·
            refine ⟨4995166854478809235814599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6660222472638412314419465 4995166854478809235814599)
            ·
              refine ⟨7492750281718213853721899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4995166854478809235814599 7492750281718213853721899)
              ·
                refine ⟨11239125422577320780582849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7492750281718213853721899 11239125422577320780582849)
                ·
                  refine ⟨8429344066932990585437137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11239125422577320780582849 8429344066932990585437137)
                  ·
                    refine ⟨6322008050199742939077853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8429344066932990585437137 6322008050199742939077853)
                    ·
                      refine ⟨2370753018824903602154195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6322008050199742939077853 2370753018824903602154195)
                      ·
                        rfl

theorem cell23_4617025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4617025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617025 prefixEnd_4617025 := by exact prefixLift 4617025
  have htrace : WordTrace (prefixWord ++ tailWord_4617025) baseStart_4617025 baseEnd_4617025 := by
    simpa [prefixWord, tailWord_4617025, baseEnd_4617025] using wordTrace_append hprefix tailTrace_4617025
  have hstable : (prefixWord ++ tailWord_4617025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617025).length < 2 ^ (prefixWord ++ tailWord_4617025).sum := by decide
  have hdescent : baseEnd_4617025 < baseStart_4617025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617041 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 1, 5]
def baseStart_4617041 : Nat := 118140960795 + 4617041 * 2 ^ 59
def prefixEnd_4617041 : Nat := 4983230072969 + 3 ^ 40 * 4617041 * 2
def baseEnd_4617041 : Nat := 790253744838458513184707

theorem tailTrace_4617041 : CollatzResearch.WordTrace tailWord_4617041 prefixEnd_4617041 790253744838458513184707 := by
  unfold tailWord_4617041
  simp only [CollatzResearch.WordTrace]
  refine ⟨168397319666256459670002977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112264879777504306446668651 168397319666256459670002977)
  ·
    refine ⟨126297989749692344752502233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168397319666256459670002977 126297989749692344752502233)
    ·
      refine ⟨94723492312269258564376675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126297989749692344752502233 94723492312269258564376675)
      ·
        refine ⟨142085238468403887846565013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94723492312269258564376675 142085238468403887846565013)
        ·
          refine ⟨6660245553206432242807735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 142085238468403887846565013 6660245553206432242807735)
          ·
            refine ⟨9990368329809648364211603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6660245553206432242807735 9990368329809648364211603)
            ·
              refine ⟨14985552494714472546317405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9990368329809648364211603 14985552494714472546317405)
              ·
                refine ⟨5619582185517927204869027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14985552494714472546317405 5619582185517927204869027)
                ·
                  refine ⟨8429373278276890807303541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5619582185517927204869027 8429373278276890807303541)
                  ·
                    refine ⟨790253744838458513184707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8429373278276890807303541 790253744838458513184707)
                    ·
                      rfl

theorem cell23_4617041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_4617041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617041 prefixEnd_4617041 := by exact prefixLift 4617041
  have htrace : WordTrace (prefixWord ++ tailWord_4617041) baseStart_4617041 baseEnd_4617041 := by
    simpa [prefixWord, tailWord_4617041, baseEnd_4617041] using wordTrace_append hprefix tailTrace_4617041
  have hstable : (prefixWord ++ tailWord_4617041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617041).length < 2 ^ (prefixWord ++ tailWord_4617041).sum := by decide
  have hdescent : baseEnd_4617041 < baseStart_4617041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617064 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4617064 : Nat := 118140960795 + 4617064 * 2 ^ 59
def prefixEnd_4617064 : Nat := 4983230072969 + 3 ^ 40 * 4617064 * 2
def baseEnd_4617064 : Nat := 2370773044570428949566515

theorem tailTrace_4617064 : CollatzResearch.WordTrace tailWord_4617064 prefixEnd_4617064 2370773044570428949566515 := by
  unfold tailWord_4617064
  simp only [CollatzResearch.WordTrace]
  refine ⟨84199079272586567299045123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112265439030115423065393497 84199079272586567299045123)
  ·
    refine ⟨126298618908879850948567685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84199079272586567299045123 126298618908879850948567685)
    ·
      refine ⟨23680991045414972052856441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126298618908879850948567685 23680991045414972052856441)
      ·
        refine ⟨17760743284061229039642331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23680991045414972052856441 17760743284061229039642331)
        ·
          refine ⟨26641114926091843559463497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17760743284061229039642331 26641114926091843559463497)
          ·
            refine ⟨19980836194568882669597623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26641114926091843559463497 19980836194568882669597623)
            ·
              refine ⟨29971254291853324004396435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19980836194568882669597623 29971254291853324004396435)
              ·
                refine ⟨44956881437779986006594653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29971254291853324004396435 44956881437779986006594653)
                ·
                  refine ⟨16858830539167494752472995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44956881437779986006594653 16858830539167494752472995)
                  ·
                    refine ⟨25288245808751242128709493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16858830539167494752472995 25288245808751242128709493)
                    ·
                      refine ⟨2370773044570428949566515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25288245808751242128709493 2370773044570428949566515)
                      ·
                        rfl

theorem cell23_4617064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4617064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617064 prefixEnd_4617064 := by exact prefixLift 4617064
  have htrace : WordTrace (prefixWord ++ tailWord_4617064) baseStart_4617064 baseEnd_4617064 := by
    simpa [prefixWord, tailWord_4617064, baseEnd_4617064] using wordTrace_append hprefix tailTrace_4617064
  have hstable : (prefixWord ++ tailWord_4617064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617064).length < 2 ^ (prefixWord ++ tailWord_4617064).sum := by decide
  have hdescent : baseEnd_4617064 < baseStart_4617064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617078 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4617078 : Nat := 118140960795 + 4617078 * 2 ^ 59
def prefixEnd_4617078 : Nat := 4983230072969 + 3 ^ 40 * 4617078 * 2
def baseEnd_4617078 : Nat := 2370780233299591894791451

theorem tailTrace_4617078 : CollatzResearch.WordTrace tailWord_4617078 prefixEnd_4617078 2370780233299591894791451 := by
  unfold tailWord_4617078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10524916822945150936818743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112265779444748276659399925 10524916822945150936818743)
  ·
    refine ⟨15787375234417726405228115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10524916822945150936818743 15787375234417726405228115)
    ·
      refine ⟨23681062851626589607842173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15787375234417726405228115 23681062851626589607842173)
      ·
        refine ⟨8880398569359971102940815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23681062851626589607842173 8880398569359971102940815)
        ·
          refine ⟨13320597854039956654411223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8880398569359971102940815 13320597854039956654411223)
          ·
            refine ⟨19980896781059934981616835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13320597854039956654411223 19980896781059934981616835)
            ·
              refine ⟨29971345171589902472425253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19980896781059934981616835 29971345171589902472425253)
              ·
                refine ⟨5619627219673106713579735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29971345171589902472425253 5619627219673106713579735)
                ·
                  refine ⟨8429440829509660070369603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5619627219673106713579735 8429440829509660070369603)
                  ·
                    refine ⟨12644161244264490105554405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8429440829509660070369603 12644161244264490105554405)
                    ·
                      refine ⟨2370780233299591894791451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12644161244264490105554405 2370780233299591894791451)
                      ·
                        rfl

theorem cell23_4617078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4617078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617078 prefixEnd_4617078 := by exact prefixLift 4617078
  have htrace : WordTrace (prefixWord ++ tailWord_4617078) baseStart_4617078 baseEnd_4617078 := by
    simpa [prefixWord, tailWord_4617078, baseEnd_4617078] using wordTrace_append hprefix tailTrace_4617078
  have hstable : (prefixWord ++ tailWord_4617078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617078).length < 2 ^ (prefixWord ++ tailWord_4617078).sum := by decide
  have hdescent : baseEnd_4617078 < baseStart_4617078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617081 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 1, 2, 3]
def baseStart_4617081 : Nat := 118140960795 + 4617081 * 2 ^ 59
def prefixEnd_4617081 : Nat := 4983230072969 + 3 ^ 40 * 4617081 * 2
def baseEnd_4617081 : Nat := 2370781773741555383053937

theorem tailTrace_4617081 : CollatzResearch.WordTrace tailWord_4617081 prefixEnd_4617081 2370781773741555383053937 := by
  unfold tailWord_4617081
  simp only [CollatzResearch.WordTrace]
  refine ⟨168398778586111546501459097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112265852390741031000972731 168398778586111546501459097)
  ·
    refine ⟨126299083939583659876094323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168398778586111546501459097 126299083939583659876094323)
    ·
      refine ⟨189448625909375489814141485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126299083939583659876094323 189448625909375489814141485)
      ·
        refine ⟨71043234716015808680303057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189448625909375489814141485 71043234716015808680303057)
        ·
          refine ⟨53282426037011856510227293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71043234716015808680303057 53282426037011856510227293)
          ·
            refine ⟨19980909763879446191335235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53282426037011856510227293 19980909763879446191335235)
            ·
              refine ⟨29971364645819169287002853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19980909763879446191335235 29971364645819169287002853)
              ·
                refine ⟨5619630871091094241313035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29971364645819169287002853 5619630871091094241313035)
                ·
                  refine ⟨8429446306636641361969553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5619630871091094241313035 8429446306636641361969553)
                  ·
                    refine ⟨6322084729977481021477165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8429446306636641361969553 6322084729977481021477165)
                    ·
                      refine ⟨2370781773741555383053937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6322084729977481021477165 2370781773741555383053937)
                      ·
                        rfl

theorem cell23_4617081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_4617081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617081 prefixEnd_4617081 := by exact prefixLift 4617081
  have htrace : WordTrace (prefixWord ++ tailWord_4617081) baseStart_4617081 baseEnd_4617081 := by
    simpa [prefixWord, tailWord_4617081, baseEnd_4617081] using wordTrace_append hprefix tailTrace_4617081
  have hstable : (prefixWord ++ tailWord_4617081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617081).length < 2 ^ (prefixWord ++ tailWord_4617081).sum := by decide
  have hdescent : baseEnd_4617081 < baseStart_4617081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617098 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_4617098 : Nat := 118140960795 + 4617098 * 2 ^ 59
def prefixEnd_4617098 : Nat := 4983230072969 + 3 ^ 40 * 4617098 * 2
def baseEnd_4617098 : Nat := 2370790502912681816541359

theorem tailTrace_4617098 : CollatzResearch.WordTrace tailWord_4617098 prefixEnd_4617098 2370790502912681816541359 := by
  unfold tailWord_4617098
  simp only [CollatzResearch.WordTrace]
  refine ⟨42099849656762489601206987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112266265751366638936551965 42099849656762489601206987)
  ·
    refine ⟨63149774485143734401810481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42099849656762489601206987 63149774485143734401810481)
    ·
      refine ⟨47362330863857800801357861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63149774485143734401810481 47362330863857800801357861)
      ·
        refine ⟨8880437036973337650254599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47362330863857800801357861 8880437036973337650254599)
        ·
          refine ⟨13320655555460006475381899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8880437036973337650254599 13320655555460006475381899)
          ·
            refine ⟨19980983333190009713072849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13320655555460006475381899 19980983333190009713072849)
            ·
              refine ⟨14985737499892507284804637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19980983333190009713072849 14985737499892507284804637)
              ·
                refine ⟨5619651562459690231801739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14985737499892507284804637 5619651562459690231801739)
                ·
                  refine ⟨8429477343689535347702609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5619651562459690231801739 8429477343689535347702609)
                  ·
                    refine ⟨6322108007767151510776957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8429477343689535347702609 6322108007767151510776957)
                    ·
                      refine ⟨2370790502912681816541359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6322108007767151510776957 2370790502912681816541359)
                      ·
                        rfl

theorem cell23_4617098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_4617098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617098 prefixEnd_4617098 := by exact prefixLift 4617098
  have htrace : WordTrace (prefixWord ++ tailWord_4617098) baseStart_4617098 baseEnd_4617098 := by
    simpa [prefixWord, tailWord_4617098, baseEnd_4617098] using wordTrace_append hprefix tailTrace_4617098
  have hstable : (prefixWord ++ tailWord_4617098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617098).length < 2 ^ (prefixWord ++ tailWord_4617098).sum := by decide
  have hdescent : baseEnd_4617098 < baseStart_4617098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617111 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 4, 1, 3]
def baseStart_4617111 : Nat := 118140960795 + 4617111 * 2 ^ 59
def prefixEnd_4617111 : Nat := 4983230072969 + 3 ^ 40 * 4617111 * 2
def baseEnd_4617111 : Nat := 2370797178161190265678799

theorem tailTrace_4617111 : CollatzResearch.WordTrace tailWord_4617111 prefixEnd_4617111 2370797178161190265678799 := by
  unfold tailWord_4617111
  simp only [CollatzResearch.WordTrace]
  refine ⟨168399872776002861625051187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112266581850668574416700791 168399872776002861625051187)
  ·
    refine ⟨252599809164004292437576781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168399872776002861625051187 252599809164004292437576781)
    ·
      refine ⟨94724928436501609664091293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252599809164004292437576781 94724928436501609664091293)
      ·
        refine ⟨35521848163688103624034235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94724928436501609664091293 35521848163688103624034235)
        ·
          refine ⟨53282772245532155436051353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35521848163688103624034235 53282772245532155436051353)
          ·
            refine ⟨39962079184149116577038515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53282772245532155436051353 39962079184149116577038515)
            ·
              refine ⟨59943118776223674865557773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39962079184149116577038515 59943118776223674865557773)
              ·
                refine ⟨22478669541083878074584165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59943118776223674865557773 22478669541083878074584165)
                ·
                  refine ⟨4214750538953227138984531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22478669541083878074584165 4214750538953227138984531)
                  ·
                    refine ⟨6322125808429840708476797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4214750538953227138984531 6322125808429840708476797)
                    ·
                      refine ⟨2370797178161190265678799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6322125808429840708476797 2370797178161190265678799)
                      ·
                        rfl

theorem cell23_4617111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_4617111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617111 prefixEnd_4617111 := by exact prefixLift 4617111
  have htrace : WordTrace (prefixWord ++ tailWord_4617111) baseStart_4617111 baseEnd_4617111 := by
    simpa [prefixWord, tailWord_4617111, baseEnd_4617111] using wordTrace_append hprefix tailTrace_4617111
  have hstable : (prefixWord ++ tailWord_4617111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617111).length < 2 ^ (prefixWord ++ tailWord_4617111).sum := by decide
  have hdescent : baseEnd_4617111 < baseStart_4617111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617142 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4617142 : Nat := 118140960795 + 4617142 * 2 ^ 59
def prefixEnd_4617142 : Nat := 4983230072969 + 3 ^ 40 * 4617142 * 2
def baseEnd_4617142 : Nat := 2370813096061479644391157

theorem tailTrace_4617142 : CollatzResearch.WordTrace tailWord_4617142 prefixEnd_4617142 2370813096061479644391157 := by
  unfold tailWord_4617142
  simp only [CollatzResearch.WordTrace]
  refine ⟨10525062714930659619964355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112267335625927035946286453 10525062714930659619964355)
  ·
    refine ⟨15787594072395989429946533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10525062714930659619964355 15787594072395989429946533)
    ·
      refine ⟨2960173888574248018114975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15787594072395989429946533 2960173888574248018114975)
      ·
        refine ⟨4440260832861372027172463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960173888574248018114975 4440260832861372027172463)
        ·
          refine ⟨6660391249292058040758695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4440260832861372027172463 6660391249292058040758695)
          ·
            refine ⟨9990586873938087061138043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6660391249292058040758695 9990586873938087061138043)
            ·
              refine ⟨14985880310907130591707065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9990586873938087061138043 14985880310907130591707065)
              ·
                refine ⟨11239410233180347943780299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14985880310907130591707065 11239410233180347943780299)
                ·
                  refine ⟨16859115349770521915670449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11239410233180347943780299 16859115349770521915670449)
                  ·
                    refine ⟨12644336512327891436752837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16859115349770521915670449 12644336512327891436752837)
                    ·
                      refine ⟨2370813096061479644391157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12644336512327891436752837 2370813096061479644391157)
                      ·
                        rfl

theorem cell23_4617142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4617142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617142 prefixEnd_4617142 := by exact prefixLift 4617142
  have htrace : WordTrace (prefixWord ++ tailWord_4617142) baseStart_4617142 baseEnd_4617142 := by
    simpa [prefixWord, tailWord_4617142, baseEnd_4617142] using wordTrace_append hprefix tailTrace_4617142
  have hstable : (prefixWord ++ tailWord_4617142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617142).length < 2 ^ (prefixWord ++ tailWord_4617142).sum := by decide
  have hdescent : baseEnd_4617142 < baseStart_4617142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617181 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_4617181 : Nat := 118140960795 + 4617181 * 2 ^ 59
def prefixEnd_4617181 : Nat := 4983230072969 + 3 ^ 40 * 4617181 * 2
def baseEnd_4617181 : Nat := 2370833121807004991803477

theorem tailTrace_4617181 : CollatzResearch.WordTrace tailWord_4617181 prefixEnd_4617181 2370833121807004991803477 := by
  unfold tailWord_4617181
  simp only [CollatzResearch.WordTrace]
  refine ⟨168402425885749263580099397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112268283923832842386732931 168402425885749263580099397)
  ·
    refine ⟨31575454853577986921268637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168402425885749263580099397 31575454853577986921268637)
    ·
      refine ⟨11840795570091745095475739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31575454853577986921268637 11840795570091745095475739)
      ·
        refine ⟨17761193355137617643213609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11840795570091745095475739 17761193355137617643213609)
        ·
          refine ⟨13320895016353213232410207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17761193355137617643213609 13320895016353213232410207)
          ·
            refine ⟨19981342524529819848615311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13320895016353213232410207 19981342524529819848615311)
            ·
              refine ⟨29972013786794729772922967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19981342524529819848615311 29972013786794729772922967)
              ·
                refine ⟨44958020680192094659384451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29972013786794729772922967 44958020680192094659384451)
                ·
                  refine ⟨67437031020288141989076677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44958020680192094659384451 67437031020288141989076677)
                  ·
                    refine ⟨12644443316304026622951877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67437031020288141989076677 12644443316304026622951877)
                    ·
                      refine ⟨2370833121807004991803477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12644443316304026622951877 2370833121807004991803477)
                      ·
                        rfl

theorem cell23_4617181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_4617181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617181 prefixEnd_4617181 := by exact prefixLift 4617181
  have htrace : WordTrace (prefixWord ++ tailWord_4617181) baseStart_4617181 baseEnd_4617181 := by
    simpa [prefixWord, tailWord_4617181, baseEnd_4617181] using wordTrace_append hprefix tailTrace_4617181
  have hstable : (prefixWord ++ tailWord_4617181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617181).length < 2 ^ (prefixWord ++ tailWord_4617181).sum := by decide
  have hdescent : baseEnd_4617181 < baseStart_4617181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617191 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 7]
def baseStart_4617191 : Nat := 118140960795 + 4617191 * 2 ^ 59
def prefixEnd_4617191 : Nat := 4983230072969 + 3 ^ 40 * 4617191 * 2
def baseEnd_4617191 : Nat := 263426472957061105853159

theorem tailTrace_4617191 : CollatzResearch.WordTrace tailWord_4617191 prefixEnd_4617191 263426472957061105853159 := by
  unfold tailWord_4617191
  simp only [CollatzResearch.WordTrace]
  refine ⟨168402790615713035287963427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112268527077142023525308951 168402790615713035287963427)
  ·
    refine ⟨252604185923569552931945141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168402790615713035287963427 252604185923569552931945141)
    ·
      refine ⟨23681642430334645587369857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 252604185923569552931945141 23681642430334645587369857)
      ·
        refine ⟨17761231822750984190527393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23681642430334645587369857 17761231822750984190527393)
        ·
          refine ⟨13320923867063238142895545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17761231822750984190527393 13320923867063238142895545)
          ·
            refine ⟨9990692900297428607171659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13320923867063238142895545 9990692900297428607171659)
            ·
              refine ⟨14986039350446142910757489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9990692900297428607171659 14986039350446142910757489)
              ·
                refine ⟨11239529512834607183068117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14986039350446142910757489 11239529512834607183068117)
                ·
                  refine ⟨263426472957061105853159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11239529512834607183068117 263426472957061105853159)
                  ·
                    rfl

theorem cell23_4617191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 7].length) (baseStart_4617191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617191 prefixEnd_4617191 := by exact prefixLift 4617191
  have htrace : WordTrace (prefixWord ++ tailWord_4617191) baseStart_4617191 baseEnd_4617191 := by
    simpa [prefixWord, tailWord_4617191, baseEnd_4617191] using wordTrace_append hprefix tailTrace_4617191
  have hstable : (prefixWord ++ tailWord_4617191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617191).length < 2 ^ (prefixWord ++ tailWord_4617191).sum := by decide
  have hdescent : baseEnd_4617191 < baseStart_4617191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617264 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 10]
def baseStart_4617264 : Nat := 118140960795 + 4617264 * 2 ^ 59
def prefixEnd_4617264 : Nat := 4983230072969 + 3 ^ 40 * 4617264 * 2
def baseEnd_4617264 : Nat := 263430637855703129673955

theorem tailTrace_4617264 : CollatzResearch.WordTrace tailWord_4617264 prefixEnd_4617264 263430637855703129673955 := by
  unfold tailWord_4617264
  simp only [CollatzResearch.WordTrace]
  refine ⟨84202726572224284377685423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112270302096299045836913897 84202726572224284377685423)
  ·
    refine ⟨126304089858336426566528135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84202726572224284377685423 126304089858336426566528135)
    ·
      refine ⟨189456134787504639849792203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126304089858336426566528135 189456134787504639849792203)
      ·
        refine ⟨284184202181256959774688305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189456134787504639849792203 284184202181256959774688305)
        ·
          refine ⟨213138151635942719831016229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284184202181256959774688305 213138151635942719831016229)
          ·
            refine ⟨39963403431739259968315543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213138151635942719831016229 39963403431739259968315543)
            ·
              refine ⟨59945105147608889952473315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39963403431739259968315543 59945105147608889952473315)
              ·
                refine ⟨89917657721413334928709973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59945105147608889952473315 89917657721413334928709973)
                ·
                  refine ⟨263430637855703129673955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89917657721413334928709973 263430637855703129673955)
                  ·
                    rfl

theorem cell23_4617264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 10].length) (baseStart_4617264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617264 prefixEnd_4617264 := by exact prefixLift 4617264
  have htrace : WordTrace (prefixWord ++ tailWord_4617264) baseStart_4617264 baseEnd_4617264 := by
    simpa [prefixWord, tailWord_4617264, baseEnd_4617264] using wordTrace_append hprefix tailTrace_4617264
  have hstable : (prefixWord ++ tailWord_4617264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617264).length < 2 ^ (prefixWord ++ tailWord_4617264).sum := by decide
  have hdescent : baseEnd_4617264 < baseStart_4617264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617298 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 6]
def baseStart_4617298 : Nat := 118140960795 + 4617298 * 2 ^ 59
def prefixEnd_4617298 : Nat := 4983230072969 + 3 ^ 40 * 4617298 * 2
def baseEnd_4617298 : Nat := 263432577671509003782271

theorem tailTrace_4617298 : CollatzResearch.WordTrace tailWord_4617298 prefixEnd_4617298 263432577671509003782271 := by
  unfold tailWord_4617298
  simp only [CollatzResearch.WordTrace]
  refine ⟨42101673306581348140527137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112271128817550261708072365 42101673306581348140527137)
  ·
    refine ⟨31576254979936011105395353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42101673306581348140527137 31576254979936011105395353)
    ·
      refine ⟨23682191234952008329046515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31576254979936011105395353 23682191234952008329046515)
      ·
        refine ⟨35523286852428012493569773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23682191234952008329046515 35523286852428012493569773)
        ·
          refine ⟨13321232569660504685088665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35523286852428012493569773 13321232569660504685088665)
          ·
            refine ⟨9990924427245378513816499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13321232569660504685088665 9990924427245378513816499)
            ·
              refine ⟨14986386640868067770724749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9990924427245378513816499 14986386640868067770724749)
              ·
                refine ⟨5619894990325525414021781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14986386640868067770724749 5619894990325525414021781)
                ·
                  refine ⟨263432577671509003782271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5619894990325525414021781 263432577671509003782271)
                  ·
                    rfl

theorem cell23_4617298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_4617298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617298 prefixEnd_4617298 := by exact prefixLift 4617298
  have htrace : WordTrace (prefixWord ++ tailWord_4617298) baseStart_4617298 baseEnd_4617298 := by
    simpa [prefixWord, tailWord_4617298, baseEnd_4617298] using wordTrace_append hprefix tailTrace_4617298
  have hstable : (prefixWord ++ tailWord_4617298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617298).length < 2 ^ (prefixWord ++ tailWord_4617298).sum := by decide
  have hdescent : baseEnd_4617298 < baseStart_4617298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617311 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 3, 5]
def baseStart_4617311 : Nat := 118140960795 + 4617311 * 2 ^ 59
def prefixEnd_4617311 : Nat := 4983230072969 + 3 ^ 40 * 4617311 * 2
def baseEnd_4617311 : Nat := 790299958097363161059293

theorem tailTrace_4617311 : CollatzResearch.WordTrace tailWord_4617311 prefixEnd_4617311 790299958097363161059293 := by
  unfold tailWord_4617311
  simp only [CollatzResearch.WordTrace]
  refine ⟨168407167375278295782331787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112271444916852197188221191 168407167375278295782331787)
  ·
    refine ⟨252610751062917443673497681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168407167375278295782331787 252610751062917443673497681)
    ·
      refine ⟨189458063297188082755123261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252610751062917443673497681 189458063297188082755123261)
      ·
        refine ⟨71046773736445531033171223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189458063297188082755123261 71046773736445531033171223)
        ·
          refine ⟨106570160604668296549756835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71046773736445531033171223 106570160604668296549756835)
          ·
            refine ⟨159855240907002444824635253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106570160604668296549756835 159855240907002444824635253)
            ·
              refine ⟨14986428835031479202309555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159855240907002444824635253 14986428835031479202309555)
              ·
                refine ⟨22479643252547218803464333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14986428835031479202309555 22479643252547218803464333)
                ·
                  refine ⟨8429866219705207051299125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22479643252547218803464333 8429866219705207051299125)
                  ·
                    refine ⟨790299958097363161059293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8429866219705207051299125 790299958097363161059293)
                    ·
                      rfl

theorem cell23_4617311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_4617311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617311 prefixEnd_4617311 := by exact prefixLift 4617311
  have htrace : WordTrace (prefixWord ++ tailWord_4617311) baseStart_4617311 baseEnd_4617311 := by
    simpa [prefixWord, tailWord_4617311, baseEnd_4617311] using wordTrace_append hprefix tailTrace_4617311
  have hstable : (prefixWord ++ tailWord_4617311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617311).length < 2 ^ (prefixWord ++ tailWord_4617311).sum := by decide
  have hdescent : baseEnd_4617311 < baseStart_4617311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617341 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_4617341 : Nat := 118140960795 + 4617341 * 2 ^ 59
def prefixEnd_4617341 : Nat := 4983230072969 + 3 ^ 40 * 4617341 * 2
def baseEnd_4617341 : Nat := 790305092903908121934247

theorem tailTrace_4617341 : CollatzResearch.WordTrace tailWord_4617341 prefixEnd_4617341 790305092903908121934247 := by
  unfold tailWord_4617341
  simp only [CollatzResearch.WordTrace]
  refine ⟨168408261565169610905923877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112272174376779740603949251 168408261565169610905923877)
  ·
    refine ⟨31576549043469302044860727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168408261565169610905923877 31576549043469302044860727)
    ·
      refine ⟨47364823565203953067291091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31576549043469302044860727 47364823565203953067291091)
      ·
        refine ⟨71047235347805929600936637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47364823565203953067291091 71047235347805929600936637)
        ·
          refine ⟨26642713255427223600351239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71047235347805929600936637 26642713255427223600351239)
          ·
            refine ⟨39964069883140835400526859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26642713255427223600351239 39964069883140835400526859)
            ·
              refine ⟨59946104824711253100790289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39964069883140835400526859 59946104824711253100790289)
              ·
                refine ⟨44959578618533439825592717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59946104824711253100790289 44959578618533439825592717)
                ·
                  refine ⟨16859841981950039934597269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44959578618533439825592717 16859841981950039934597269)
                  ·
                    refine ⟨790305092903908121934247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16859841981950039934597269 790305092903908121934247)
                    ·
                      rfl

theorem cell23_4617341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_4617341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617341 prefixEnd_4617341 := by exact prefixLift 4617341
  have htrace : WordTrace (prefixWord ++ tailWord_4617341) baseStart_4617341 baseEnd_4617341 := by
    simpa [prefixWord, tailWord_4617341, baseEnd_4617341] using wordTrace_append hprefix tailTrace_4617341
  have hstable : (prefixWord ++ tailWord_4617341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617341).length < 2 ^ (prefixWord ++ tailWord_4617341).sum := by decide
  have hdescent : baseEnd_4617341 < baseStart_4617341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617348 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4617348 : Nat := 118140960795 + 4617348 * 2 ^ 59
def prefixEnd_4617348 : Nat := 4983230072969 + 3 ^ 40 * 4617348 * 2
def baseEnd_4617348 : Nat := 2370918873076305838415209

theorem tailTrace_4617348 : CollatzResearch.WordTrace tailWord_4617348 prefixEnd_4617348 2370918873076305838415209 := by
  unfold tailWord_4617348
  simp only [CollatzResearch.WordTrace]
  refine ⟨84204258438072125550714349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112272344584096167400952465 84204258438072125550714349)
  ·
    refine ⟨31576596914277047081517881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84204258438072125550714349 31576596914277047081517881)
    ·
      refine ⟨23682447685707785311138411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31576596914277047081517881 23682447685707785311138411)
      ·
        refine ⟨35523671528561677966707617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23682447685707785311138411 35523671528561677966707617)
        ·
          refine ⟨26642753646421258475030713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35523671528561677966707617 26642753646421258475030713)
          ·
            refine ⟨19982065234815943856273035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26642753646421258475030713 19982065234815943856273035)
            ·
              refine ⟨29973097852223915784409553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19982065234815943856273035 29973097852223915784409553)
              ·
                refine ⟨22479823389167936838307165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29973097852223915784409553 22479823389167936838307165)
                ·
                  refine ⟨8429933770937976314365187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22479823389167936838307165 8429933770937976314365187)
                  ·
                    refine ⟨12644900656406964471547781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8429933770937976314365187 12644900656406964471547781)
                    ·
                      refine ⟨2370918873076305838415209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12644900656406964471547781 2370918873076305838415209)
                      ·
                        rfl

theorem cell23_4617348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4617348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617348 prefixEnd_4617348 := by exact prefixLift 4617348
  have htrace : WordTrace (prefixWord ++ tailWord_4617348) baseStart_4617348 baseEnd_4617348 := by
    simpa [prefixWord, tailWord_4617348, baseEnd_4617348] using wordTrace_append hprefix tailTrace_4617348
  have hstable : (prefixWord ++ tailWord_4617348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617348).length < 2 ^ (prefixWord ++ tailWord_4617348).sum := by decide
  have hdescent : baseEnd_4617348 < baseStart_4617348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617351 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_4617351 : Nat := 118140960795 + 4617351 * 2 ^ 59
def prefixEnd_4617351 : Nat := 4983230072969 + 3 ^ 40 * 4617351 * 2
def baseEnd_4617351 : Nat := 2370920413518269326677695

theorem tailTrace_4617351 : CollatzResearch.WordTrace tailWord_4617351 prefixEnd_4617351 2370920413518269326677695 := by
  unfold tailWord_4617351
  simp only [CollatzResearch.WordTrace]
  refine ⟨168408626295133382613787907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112272417530088921742525271 168408626295133382613787907)
  ·
    refine ⟨252612939442700073920681861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168408626295133382613787907 252612939442700073920681861)
    ·
      refine ⟨47364926145506263860127849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252612939442700073920681861 47364926145506263860127849)
      ·
        refine ⟨35523694609129697895095887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47364926145506263860127849 35523694609129697895095887)
        ·
          refine ⟨53285541913694546842643831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35523694609129697895095887 53285541913694546842643831)
          ·
            refine ⟨79928312870541820263965747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53285541913694546842643831 79928312870541820263965747)
            ·
              refine ⟨119892469305812730395948621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79928312870541820263965747 119892469305812730395948621)
              ·
                refine ⟨44959675989679773898480733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119892469305812730395948621 44959675989679773898480733)
                ·
                  refine ⟨16859878496129915211930275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44959675989679773898480733 16859878496129915211930275)
                  ·
                    refine ⟨25289817744194872817895413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16859878496129915211930275 25289817744194872817895413)
                    ·
                      refine ⟨2370920413518269326677695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25289817744194872817895413 2370920413518269326677695)
                      ·
                        rfl

theorem cell23_4617351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_4617351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617351 prefixEnd_4617351 := by exact prefixLift 4617351
  have htrace : WordTrace (prefixWord ++ tailWord_4617351) baseStart_4617351 baseEnd_4617351 := by
    simpa [prefixWord, tailWord_4617351, baseEnd_4617351] using wordTrace_append hprefix tailTrace_4617351
  have hstable : (prefixWord ++ tailWord_4617351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617351).length < 2 ^ (prefixWord ++ tailWord_4617351).sum := by decide
  have hdescent : baseEnd_4617351 < baseStart_4617351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617358 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_4617358 : Nat := 118140960795 + 4617358 * 2 ^ 59
def prefixEnd_4617358 : Nat := 4983230072969 + 3 ^ 40 * 4617358 * 2
def baseEnd_4617358 : Nat := 790308002627616933096721

theorem tailTrace_4617358 : CollatzResearch.WordTrace tailWord_4617358 prefixEnd_4617358 790308002627616933096721 := by
  unfold tailWord_4617358
  simp only [CollatzResearch.WordTrace]
  refine ⟨21051110200763502851161591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112272587737405348539528485 21051110200763502851161591)
  ·
    refine ⟨31576665301145254276742387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21051110200763502851161591 31576665301145254276742387)
    ·
      refine ⟨47364997951717881415113581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31576665301145254276742387 47364997951717881415113581)
      ·
        refine ⟨17761874231894205530667593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47364997951717881415113581 17761874231894205530667593)
        ·
          refine ⟨13321405673920654148000695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17761874231894205530667593 13321405673920654148000695)
          ·
            refine ⟨19982108510880981222001043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13321405673920654148000695 19982108510880981222001043)
            ·
              refine ⟨29973162766321471833001565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19982108510880981222001043 29973162766321471833001565)
              ·
                refine ⟨11239936037370551937375587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29973162766321471833001565 11239936037370551937375587)
                ·
                  refine ⟨16859904056055827906063381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11239936037370551937375587 16859904056055827906063381)
                  ·
                    refine ⟨790308002627616933096721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16859904056055827906063381 790308002627616933096721)
                    ·
                      rfl

theorem cell23_4617358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_4617358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617358 prefixEnd_4617358 := by exact prefixLift 4617358
  have htrace : WordTrace (prefixWord ++ tailWord_4617358) baseStart_4617358 baseEnd_4617358 := by
    simpa [prefixWord, tailWord_4617358, baseEnd_4617358] using wordTrace_append hprefix tailTrace_4617358
  have hstable : (prefixWord ++ tailWord_4617358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617358).length < 2 ^ (prefixWord ++ tailWord_4617358).sum := by decide
  have hdescent : baseEnd_4617358 < baseStart_4617358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617409 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 2, 4]
def baseStart_4617409 : Nat := 118140960795 + 4617409 * 2 ^ 59
def prefixEnd_4617409 : Nat := 4983230072969 + 3 ^ 40 * 4617409 * 2
def baseEnd_4617409 : Nat := 790316731798743366584143

theorem tailTrace_4617409 : CollatzResearch.WordTrace tailWord_4617409 prefixEnd_4617409 790316731798743366584143 := by
  unfold tailWord_4617409
  simp only [CollatzResearch.WordTrace]
  refine ⟨168410741728923258519399281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112273827819282172346266187 168410741728923258519399281)
  ·
    refine ⟨126308056296692443889549461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168410741728923258519399281 126308056296692443889549461)
    ·
      refine ⟨5920690138907458307322631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 126308056296692443889549461 5920690138907458307322631)
      ·
        refine ⟨8881035208361187460983947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5920690138907458307322631 8881035208361187460983947)
        ·
          refine ⟨13321552812541781191475921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8881035208361187460983947 13321552812541781191475921)
          ·
            refine ⟨9991164609406335893606941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13321552812541781191475921 9991164609406335893606941)
            ·
              refine ⟨3746686728527375960102603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9991164609406335893606941 3746686728527375960102603)
              ·
                refine ⟨5620030092791063940153905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3746686728527375960102603 5620030092791063940153905)
                ·
                  refine ⟨4215022569593297955115429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5620030092791063940153905 4215022569593297955115429)
                  ·
                    refine ⟨790316731798743366584143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215022569593297955115429 790316731798743366584143)
                    ·
                      rfl

theorem cell23_4617409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_4617409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617409 prefixEnd_4617409 := by exact prefixLift 4617409
  have htrace : WordTrace (prefixWord ++ tailWord_4617409) baseStart_4617409 baseEnd_4617409 := by
    simpa [prefixWord, tailWord_4617409, baseEnd_4617409] using wordTrace_append hprefix tailTrace_4617409
  have hstable : (prefixWord ++ tailWord_4617409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617409).length < 2 ^ (prefixWord ++ tailWord_4617409).sum := by decide
  have hdescent : baseEnd_4617409 < baseStart_4617409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617412 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_4617412 : Nat := 118140960795 + 4617412 * 2 ^ 59
def prefixEnd_4617412 : Nat := 4983230072969 + 3 ^ 40 * 4617412 * 2
def baseEnd_4617412 : Nat := 2370951735838193588014915

theorem tailTrace_4617412 : CollatzResearch.WordTrace tailWord_4617412 prefixEnd_4617412 2370951735838193588014915 := by
  unfold tailWord_4617412
  simp only [CollatzResearch.WordTrace]
  refine ⟨84205425573956195015879245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112273900765274926687838993 84205425573956195015879245)
  ·
    refine ⟨31577034590233573130954717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84205425573956195015879245 31577034590233573130954717)
    ·
      refine ⟨11841387971337589924108019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31577034590233573130954717 11841387971337589924108019)
      ·
        refine ⟨17762081957006384886162029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11841387971337589924108019 17762081957006384886162029)
        ·
          refine ⟨6660780733877394332310761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17762081957006384886162029 6660780733877394332310761)
          ·
            refine ⟨4995585550408045749233071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6660780733877394332310761 4995585550408045749233071)
            ·
              refine ⟨7493378325612068623849607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4995585550408045749233071 7493378325612068623849607)
              ·
                refine ⟨11240067488418102935774411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7493378325612068623849607 11240067488418102935774411)
                ·
                  refine ⟨16860101232627154403661617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11240067488418102935774411 16860101232627154403661617)
                  ·
                    refine ⟨12645075924470365802746213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16860101232627154403661617 12645075924470365802746213)
                    ·
                      refine ⟨2370951735838193588014915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12645075924470365802746213 2370951735838193588014915)
                      ·
                        rfl

theorem cell23_4617412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_4617412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617412 prefixEnd_4617412 := by exact prefixLift 4617412
  have htrace : WordTrace (prefixWord ++ tailWord_4617412) baseStart_4617412 baseEnd_4617412 := by
    simpa [prefixWord, tailWord_4617412, baseEnd_4617412] using wordTrace_append hprefix tailTrace_4617412
  have hstable : (prefixWord ++ tailWord_4617412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617412).length < 2 ^ (prefixWord ++ tailWord_4617412).sum := by decide
  have hdescent : baseEnd_4617412 < baseStart_4617412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617415 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_4617415 : Nat := 118140960795 + 4617415 * 2 ^ 59
def prefixEnd_4617415 : Nat := 4983230072969 + 3 ^ 40 * 4617415 * 2
def baseEnd_4617415 : Nat := 2370953276280157076277401

theorem tailTrace_4617415 : CollatzResearch.WordTrace tailWord_4617415 prefixEnd_4617415 2370953276280157076277401 := by
  unfold tailWord_4617415
  simp only [CollatzResearch.WordTrace]
  refine ⟨168410960566901521544117699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112273973711267681029411799 168410960566901521544117699)
  ·
    refine ⟨252616440850352282316176549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168410960566901521544117699 252616440850352282316176549)
    ·
      refine ⟨47365582659441052934283103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252616440850352282316176549 47365582659441052934283103)
      ·
        refine ⟨71048373989161579401424655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47365582659441052934283103 71048373989161579401424655)
        ·
          refine ⟨106572560983742369102136983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71048373989161579401424655 106572560983742369102136983)
          ·
            refine ⟨159858841475613553653205475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106572560983742369102136983 159858841475613553653205475)
            ·
              refine ⟨239788262213420330479808213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159858841475613553653205475 239788262213420330479808213)
              ·
                refine ⟨5620037395627038995620505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 239788262213420330479808213 5620037395627038995620505)
                ·
                  refine ⟨4215028046720279246715379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5620037395627038995620505 4215028046720279246715379)
                  ·
                    refine ⟨6322542070080418870073069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4215028046720279246715379 6322542070080418870073069)
                    ·
                      refine ⟨2370953276280157076277401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6322542070080418870073069 2370953276280157076277401)
                      ·
                        rfl

theorem cell23_4617415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_4617415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617415 prefixEnd_4617415 := by exact prefixLift 4617415
  have htrace : WordTrace (prefixWord ++ tailWord_4617415) baseStart_4617415 baseEnd_4617415 := by
    simpa [prefixWord, tailWord_4617415, baseEnd_4617415] using wordTrace_append hprefix tailTrace_4617415
  have hstable : (prefixWord ++ tailWord_4617415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617415).length < 2 ^ (prefixWord ++ tailWord_4617415).sum := by decide
  have hdescent : baseEnd_4617415 < baseStart_4617415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617422 : List Nat := [4, 1, 1, 1, 6, 1, 2, 7]
def baseStart_4617422 : Nat := 118140960795 + 4617422 * 2 ^ 59
def prefixEnd_4617422 : Nat := 4983230072969 + 3 ^ 40 * 4617422 * 2
def baseEnd_4617422 : Nat := 87813217431286612921847

theorem tailTrace_4617422 : CollatzResearch.WordTrace tailWord_4617422 prefixEnd_4617422 87813217431286612921847 := by
  unfold tailWord_4617422
  simp only [CollatzResearch.WordTrace]
  refine ⟨21051401984734520217452815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112274143918584107826415013 21051401984734520217452815)
  ·
    refine ⟨31577102977101780326179223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21051401984734520217452815 31577102977101780326179223)
    ·
      refine ⟨47365654465652670489268835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31577102977101780326179223 47365654465652670489268835)
      ·
        refine ⟨71048481698479005733903253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47365654465652670489268835 71048481698479005733903253)
        ·
          refine ⟨3330397579616203393776715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71048481698479005733903253 3330397579616203393776715)
          ·
            refine ⟨4995596369424305090665073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330397579616203393776715 4995596369424305090665073)
            ·
              refine ⟨3746697277068228817998805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4995596369424305090665073 3746697277068228817998805)
              ·
                refine ⟨87813217431286612921847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3746697277068228817998805 87813217431286612921847)
                ·
                  rfl

theorem cell23_4617422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_4617422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617422 prefixEnd_4617422 := by exact prefixLift 4617422
  have htrace : WordTrace (prefixWord ++ tailWord_4617422) baseStart_4617422 baseEnd_4617422 := by
    simpa [prefixWord, tailWord_4617422, baseEnd_4617422] using wordTrace_append hprefix tailTrace_4617422
  have hstable : (prefixWord ++ tailWord_4617422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617422).length < 2 ^ (prefixWord ++ tailWord_4617422).sum := by decide
  have hdescent : baseEnd_4617422 < baseStart_4617422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617431 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 1, 8]
def baseStart_4617431 : Nat := 118140960795 + 4617431 * 2 ^ 59
def prefixEnd_4617431 : Nat := 4983230072969 + 3 ^ 40 * 4617431 * 2
def baseEnd_4617431 : Nat := 790320497323543004559109

theorem tailTrace_4617431 : CollatzResearch.WordTrace tailWord_4617431 prefixEnd_4617431 790320497323543004559109 := by
  unfold tailWord_4617431
  simp only [CollatzResearch.WordTrace]
  refine ⟨168411544134843556276700147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112274362756562370851133431 168411544134843556276700147)
  ·
    refine ⟨252617316202265334415050221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168411544134843556276700147 252617316202265334415050221)
    ·
      refine ⟨94731493575849500405643833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252617316202265334415050221 94731493575849500405643833)
      ·
        refine ⟨71048620181887125304232875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94731493575849500405643833 71048620181887125304232875)
        ·
          refine ⟨106572930272830687956349313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71048620181887125304232875 106572930272830687956349313)
          ·
            refine ⟨79929697704623015967261985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106572930272830687956349313 79929697704623015967261985)
            ·
              refine ⟨59947273278467261975446489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79929697704623015967261985 59947273278467261975446489)
              ·
                refine ⟨44960454958850446481584867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59947273278467261975446489 44960454958850446481584867)
                ·
                  refine ⟨67440682438275669722377301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44960454958850446481584867 67440682438275669722377301)
                  ·
                    refine ⟨790320497323543004559109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67440682438275669722377301 790320497323543004559109)
                    ·
                      rfl

theorem cell23_4617431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_4617431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617431 prefixEnd_4617431 := by exact prefixLift 4617431
  have htrace : WordTrace (prefixWord ++ tailWord_4617431) baseStart_4617431 baseEnd_4617431 := by
    simpa [prefixWord, tailWord_4617431, baseEnd_4617431] using wordTrace_append hprefix tailTrace_4617431
  have hstable : (prefixWord ++ tailWord_4617431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617431).length < 2 ^ (prefixWord ++ tailWord_4617431).sum := by decide
  have hdescent : baseEnd_4617431 < baseStart_4617431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617460 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4617460 : Nat := 118140960795 + 4617460 * 2 ^ 59
def prefixEnd_4617460 : Nat := 4983230072969 + 3 ^ 40 * 4617460 * 2
def baseEnd_4617460 : Nat := 790325460969869800071565

theorem tailTrace_4617460 : CollatzResearch.WordTrace tailWord_4617460 prefixEnd_4617460 790325460969869800071565 := by
  unfold tailWord_4617460
  simp only [CollatzResearch.WordTrace]
  refine ⟨84206300925869247114752917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112275067901158996153003889 84206300925869247114752917)
  ·
    refine ⟨3947170355900120958504043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84206300925869247114752917 3947170355900120958504043)
    ·
      refine ⟨5920755533850181437756065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3947170355900120958504043 5920755533850181437756065)
      ·
        refine ⟨4440566650387636078317049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5920755533850181437756065 4440566650387636078317049)
        ·
          refine ⟨3330424987790727058737787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4440566650387636078317049 3330424987790727058737787)
          ·
            refine ⟨4995637481686090588106681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330424987790727058737787 4995637481686090588106681)
            ·
              refine ⟨3746728111264567941080011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4995637481686090588106681 3746728111264567941080011)
              ·
                refine ⟨5620092166896851911620017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3746728111264567941080011 5620092166896851911620017)
                ·
                  refine ⟨4215069125172638933715013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5620092166896851911620017 4215069125172638933715013)
                  ·
                    refine ⟨790325460969869800071565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215069125172638933715013 790325460969869800071565)
                    ·
                      rfl

theorem cell23_4617460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4617460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617460 prefixEnd_4617460 := by exact prefixLift 4617460
  have htrace : WordTrace (prefixWord ++ tailWord_4617460) baseStart_4617460 baseEnd_4617460 := by
    simpa [prefixWord, tailWord_4617460, baseEnd_4617460] using wordTrace_append hprefix tailTrace_4617460
  have hstable : (prefixWord ++ tailWord_4617460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617460).length < 2 ^ (prefixWord ++ tailWord_4617460).sum := by decide
  have hdescent : baseEnd_4617460 < baseStart_4617460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617495 : List Nat := [1, 1, 3, 4, 1, 1, 2, 5, 5]
def baseStart_4617495 : Nat := 118140960795 + 4617495 * 2 ^ 59
def prefixEnd_4617495 : Nat := 4983230072969 + 3 ^ 40 * 4617495 * 2
def baseEnd_4617495 : Nat := 263443817192501862586337

theorem tailTrace_4617495 : CollatzResearch.WordTrace tailWord_4617495 prefixEnd_4617495 263443817192501862586337 := by
  unfold tailWord_4617495
  simp only [CollatzResearch.WordTrace]
  refine ⟨168413878406611695207029939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112275918937741130138019959 168413878406611695207029939)
  ·
    refine ⟨252620817609917542810544909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168413878406611695207029939 252620817609917542810544909)
    ·
      refine ⟨94732806603719078553954341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252620817609917542810544909 94732806603719078553954341)
      ·
        refine ⟨17762401238197327228866439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94732806603719078553954341 17762401238197327228866439)
        ·
          refine ⟨26643601857295990843299659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17762401238197327228866439 26643601857295990843299659)
          ·
            refine ⟨39965402785943986264949489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26643601857295990843299659 39965402785943986264949489)
            ·
              refine ⟨29974052089457989698712117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39965402785943986264949489 29974052089457989698712117)
              ·
                refine ⟨2810067383386686534254261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29974052089457989698712117 2810067383386686534254261)
                ·
                  refine ⟨263443817192501862586337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2810067383386686534254261 263443817192501862586337)
                  ·
                    rfl

theorem cell23_4617495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 5].length) (baseStart_4617495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617495 prefixEnd_4617495 := by exact prefixLift 4617495
  have htrace : WordTrace (prefixWord ++ tailWord_4617495) baseStart_4617495 baseEnd_4617495 := by
    simpa [prefixWord, tailWord_4617495, baseEnd_4617495] using wordTrace_append hprefix tailTrace_4617495
  have hstable : (prefixWord ++ tailWord_4617495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617495).length < 2 ^ (prefixWord ++ tailWord_4617495).sum := by decide
  have hdescent : baseEnd_4617495 < baseStart_4617495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617506 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_4617506 : Nat := 118140960795 + 4617506 * 2 ^ 59
def prefixEnd_4617506 : Nat := 4983230072969 + 3 ^ 40 * 4617506 * 2
def baseEnd_4617506 : Nat := 2371000003019716220239483

theorem tailTrace_4617506 : CollatzResearch.WordTrace tailWord_4617506 prefixEnd_4617506 2371000003019716220239483 := by
  unfold tailWord_4617506
  simp only [CollatzResearch.WordTrace]
  refine ⟨42103569902392961021420093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112276186406381229390453581 42103569902392961021420093)
  ·
    refine ⟨15788838713397360383032535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42103569902392961021420093 15788838713397360383032535)
    ·
      refine ⟨23683258070096040574548803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15788838713397360383032535 23683258070096040574548803)
      ·
        refine ⟨35524887105144060861823205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23683258070096040574548803 35524887105144060861823205)
        ·
          refine ⟨6660916332214511411591851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35524887105144060861823205 6660916332214511411591851)
          ·
            refine ⟨9991374498321767117387777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6660916332214511411591851 9991374498321767117387777)
            ·
              refine ⟨7493530873741325338040833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9991374498321767117387777 7493530873741325338040833)
              ·
                refine ⟨5620148155305994003530625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7493530873741325338040833 5620148155305994003530625)
                ·
                  refine ⟨4215111116479495502647969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5620148155305994003530625 4215111116479495502647969)
                  ·
                    refine ⟨3161333337359621626985977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4215111116479495502647969 3161333337359621626985977)
                    ·
                      refine ⟨2371000003019716220239483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3161333337359621626985977 2371000003019716220239483)
                      ·
                        rfl

theorem cell23_4617506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_4617506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617506 prefixEnd_4617506 := by exact prefixLift 4617506
  have htrace : WordTrace (prefixWord ++ tailWord_4617506) baseStart_4617506 baseEnd_4617506 := by
    simpa [prefixWord, tailWord_4617506, baseEnd_4617506] using wordTrace_append hprefix tailTrace_4617506
  have hstable : (prefixWord ++ tailWord_4617506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617506).length < 2 ^ (prefixWord ++ tailWord_4617506).sum := by decide
  have hdescent : baseEnd_4617506 < baseStart_4617506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617512 : List Nat := [2, 1, 5, 1, 2, 2, 1, 4, 5]
def baseStart_4617512 : Nat := 118140960795 + 4617512 * 2 ^ 59
def prefixEnd_4617512 : Nat := 4983230072969 + 3 ^ 40 * 4617512 * 2
def baseEnd_4617512 : Nat := 263444787100404799640495

theorem tailTrace_4617512 : CollatzResearch.WordTrace tailWord_4617512 prefixEnd_4617512 263444787100404799640495 := by
  unfold tailWord_4617512
  simp only [CollatzResearch.WordTrace]
  refine ⟨84207249223775053555199395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112276332298366738073599193 84207249223775053555199395)
  ·
    refine ⟨126310873835662580332799093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84207249223775053555199395 126310873835662580332799093)
    ·
      refine ⟨11841644422093366906199915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126310873835662580332799093 11841644422093366906199915)
      ·
        refine ⟨17762466633140050359299873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11841644422093366906199915 17762466633140050359299873)
        ·
          refine ⟨13321849974855037769474905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17762466633140050359299873 13321849974855037769474905)
          ·
            refine ⟨9991387481141278327106179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13321849974855037769474905 9991387481141278327106179)
            ·
              refine ⟨14987081221711917490659269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9991387481141278327106179 14987081221711917490659269)
              ·
                refine ⟨2810077729070984529498613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14987081221711917490659269 2810077729070984529498613)
                ·
                  refine ⟨263444787100404799640495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2810077729070984529498613 263444787100404799640495)
                  ·
                    rfl

theorem cell23_4617512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 5].length) (baseStart_4617512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617512 prefixEnd_4617512 := by exact prefixLift 4617512
  have htrace : WordTrace (prefixWord ++ tailWord_4617512) baseStart_4617512 baseEnd_4617512 := by
    simpa [prefixWord, tailWord_4617512, baseEnd_4617512] using wordTrace_append hprefix tailTrace_4617512
  have hstable : (prefixWord ++ tailWord_4617512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617512).length < 2 ^ (prefixWord ++ tailWord_4617512).sum := by decide
  have hdescent : baseEnd_4617512 < baseStart_4617512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617528 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_4617528 : Nat := 118140960795 + 4617528 * 2 ^ 59
def prefixEnd_4617528 : Nat := 4983230072969 + 3 ^ 40 * 4617528 * 2
def baseEnd_4617528 : Nat := 2371011299594115134164381

theorem tailTrace_4617528 : CollatzResearch.WordTrace tailWord_4617528 prefixEnd_4617528 2371011299594115134164381 := by
  unfold tailWord_4617528
  simp only [CollatzResearch.WordTrace]
  refine ⟨84207541007746070921490619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112276721343661427895320825 84207541007746070921490619)
  ·
    refine ⟨126311311511619106382235929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84207541007746070921490619 126311311511619106382235929)
    ·
      refine ⟨94733483633714329786676947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126311311511619106382235929 94733483633714329786676947)
      ·
        refine ⟨142100225450571494680015421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94733483633714329786676947 142100225450571494680015421)
        ·
          refine ⟨53287584543964310505005783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142100225450571494680015421 53287584543964310505005783)
          ·
            refine ⟨79931376815946465757508675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53287584543964310505005783 79931376815946465757508675)
            ·
              refine ⟨119897065223919698636263013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79931376815946465757508675 119897065223919698636263013)
              ·
                refine ⟨22480699729484943494299315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119897065223919698636263013 22480699729484943494299315)
                ·
                  refine ⟨33721049594227415241448973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22480699729484943494299315 33721049594227415241448973)
                  ·
                    refine ⟨12645393597835280715543365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33721049594227415241448973 12645393597835280715543365)
                    ·
                      refine ⟨2371011299594115134164381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12645393597835280715543365 2371011299594115134164381)
                      ·
                        rfl

theorem cell23_4617528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_4617528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617528 prefixEnd_4617528 := by exact prefixLift 4617528
  have htrace : WordTrace (prefixWord ++ tailWord_4617528) baseStart_4617528 baseEnd_4617528 := by
    simpa [prefixWord, tailWord_4617528, baseEnd_4617528] using wordTrace_append hprefix tailTrace_4617528
  have hstable : (prefixWord ++ tailWord_4617528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617528).length < 2 ^ (prefixWord ++ tailWord_4617528).sum := by decide
  have hdescent : baseEnd_4617528 < baseStart_4617528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617545 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 4]
def baseStart_4617545 : Nat := 118140960795 + 4617545 * 2 ^ 59
def prefixEnd_4617545 : Nat := 4983230072969 + 3 ^ 40 * 4617545 * 2
def baseEnd_4617545 : Nat := 2371020028765241567651803

theorem tailTrace_4617545 : CollatzResearch.WordTrace tailWord_4617545 prefixEnd_4617545 2371020028765241567651803 := by
  unfold tailWord_4617545
  simp only [CollatzResearch.WordTrace]
  refine ⟨168415702056430553746350089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112277134704287035830900059 168415702056430553746350089)
  ·
    refine ⟨126311776542322915309762567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168415702056430553746350089 126311776542322915309762567)
    ·
      refine ⟨189467664813484372964643851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126311776542322915309762567 189467664813484372964643851)
      ·
        refine ⟨284201497220226559446965777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189467664813484372964643851 284201497220226559446965777)
        ·
          refine ⟨213151122915169919585224333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284201497220226559446965777 213151122915169919585224333)
          ·
            refine ⟨79931671093188719844459125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213151122915169919585224333 79931671093188719844459125)
            ·
              refine ⟨7493594164986442485418043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79931671093188719844459125 7493594164986442485418043)
              ·
                refine ⟨11240391247479663728127065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7493594164986442485418043 11240391247479663728127065)
                ·
                  refine ⟨8430293435609747796095299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11240391247479663728127065 8430293435609747796095299)
                  ·
                    refine ⟨12645440153414621694142949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8430293435609747796095299 12645440153414621694142949)
                    ·
                      refine ⟨2371020028765241567651803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12645440153414621694142949 2371020028765241567651803)
                      ·
                        rfl

theorem cell23_4617545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 4].length) (baseStart_4617545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617545 prefixEnd_4617545 := by exact prefixLift 4617545
  have htrace : WordTrace (prefixWord ++ tailWord_4617545) baseStart_4617545 baseEnd_4617545 := by
    simpa [prefixWord, tailWord_4617545, baseEnd_4617545] using wordTrace_append hprefix tailTrace_4617545
  have hstable : (prefixWord ++ tailWord_4617545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617545).length < 2 ^ (prefixWord ++ tailWord_4617545).sum := by decide
  have hdescent : baseEnd_4617545 < baseStart_4617545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617572 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_4617572 : Nat := 118140960795 + 4617572 * 2 ^ 59
def prefixEnd_4617572 : Nat := 4983230072969 + 3 ^ 40 * 4617572 * 2
def baseEnd_4617572 : Nat := 790344630914304320671393

theorem tailTrace_4617572 : CollatzResearch.WordTrace tailWord_4617572 prefixEnd_4617572 790344630914304320671393 := by
  unfold tailWord_4617572
  simp only [CollatzResearch.WordTrace]
  refine ⟨84208343413666368678791485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112277791218221824905055313 84208343413666368678791485)
  ·
    refine ⟨31578128780124888254546807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84208343413666368678791485 31578128780124888254546807)
    ·
      refine ⟨47367193170187332381820211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31578128780124888254546807 47367193170187332381820211)
      ·
        refine ⟨71050789755280998572730317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47367193170187332381820211 71050789755280998572730317)
        ·
          refine ⟨26644046158230374464773869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71050789755280998572730317 26644046158230374464773869)
          ·
            refine ⟨9991517309336390424290201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26644046158230374464773869 9991517309336390424290201)
            ·
              refine ⟨7493637982002292818217651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9991517309336390424290201 7493637982002292818217651)
              ·
                refine ⟨11240456973003439227326477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7493637982002292818217651 11240456973003439227326477)
                ·
                  refine ⟨4215171364876289710247429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11240456973003439227326477 4215171364876289710247429)
                  ·
                    refine ⟨790344630914304320671393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215171364876289710247429 790344630914304320671393)
                    ·
                      rfl

theorem cell23_4617572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_4617572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617572 prefixEnd_4617572 := by exact prefixLift 4617572
  have htrace : WordTrace (prefixWord ++ tailWord_4617572) baseStart_4617572 baseEnd_4617572 := by
    simpa [prefixWord, tailWord_4617572, baseEnd_4617572] using wordTrace_append hprefix tailTrace_4617572
  have hstable : (prefixWord ++ tailWord_4617572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617572).length < 2 ^ (prefixWord ++ tailWord_4617572).sum := by decide
  have hdescent : baseEnd_4617572 < baseStart_4617572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617602 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 8]
def baseStart_4617602 : Nat := 118140960795 + 4617602 * 2 ^ 59
def prefixEnd_4617602 : Nat := 4983230072969 + 3 ^ 40 * 4617602 * 2
def baseEnd_4617602 : Nat := 263449921906949760515449

theorem tailTrace_4617602 : CollatzResearch.WordTrace tailWord_4617602 prefixEnd_4617602 263449921906949760515449 := by
  unfold tailWord_4617602
  simp only [CollatzResearch.WordTrace]
  refine ⟨42104445254306013120293765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112278520678149368320783373 42104445254306013120293765)
  ·
    refine ⟨7894583485182377460055081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42104445254306013120293765 7894583485182377460055081)
    ·
      refine ⟨5920937613886783095041311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7894583485182377460055081 5920937613886783095041311)
      ·
        refine ⟨8881406420830174642561967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5920937613886783095041311 8881406420830174642561967)
        ·
          refine ⟨13322109631245261963842951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8881406420830174642561967 13322109631245261963842951)
          ·
            refine ⟨19983164446867892945764427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13322109631245261963842951 19983164446867892945764427)
            ·
              refine ⟨29974746670301839418646641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19983164446867892945764427 29974746670301839418646641)
              ·
                refine ⟨22481060002726379563984981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29974746670301839418646641 22481060002726379563984981)
                ·
                  refine ⟨263449921906949760515449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22481060002726379563984981 263449921906949760515449)
                  ·
                    rfl

theorem cell23_4617602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_4617602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617602 prefixEnd_4617602 := by exact prefixLift 4617602
  have htrace : WordTrace (prefixWord ++ tailWord_4617602) baseStart_4617602 baseEnd_4617602 := by
    simpa [prefixWord, tailWord_4617602, baseEnd_4617602] using wordTrace_append hprefix tailTrace_4617602
  have hstable : (prefixWord ++ tailWord_4617602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617602).length < 2 ^ (prefixWord ++ tailWord_4617602).sum := by decide
  have hdescent : baseEnd_4617602 < baseStart_4617602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617629 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_4617629 : Nat := 118140960795 + 4617629 * 2 ^ 59
def prefixEnd_4617629 : Nat := 4983230072969 + 3 ^ 40 * 4617629 * 2
def baseEnd_4617629 : Nat := 2371063161140219239001417

theorem tailTrace_4617629 : CollatzResearch.WordTrace tailWord_4617629 prefixEnd_4617629 2371063161140219239001417 := by
  unfold tailWord_4617629
  simp only [CollatzResearch.WordTrace]
  refine ⟨168418765788126236092407941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112279177192084157394938627 168418765788126236092407941)
  ·
    refine ⟨31578518585273669267326489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168418765788126236092407941 31578518585273669267326489)
    ·
      refine ⟨23683888938955251950494867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31578518585273669267326489 23683888938955251950494867)
      ·
        refine ⟨35525833408432877925742301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23683888938955251950494867 35525833408432877925742301)
        ·
          refine ⟨13322187528162329222153363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35525833408432877925742301 13322187528162329222153363)
          ·
            refine ⟨19983281292243493833230045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13322187528162329222153363 19983281292243493833230045)
            ·
              refine ⟨7493730484591310187461267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19983281292243493833230045 7493730484591310187461267)
              ·
                refine ⟨11240595726886965281191901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7493730484591310187461267 11240595726886965281191901)
                ·
                  refine ⟨4215223397582611980446963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11240595726886965281191901 4215223397582611980446963)
                  ·
                    refine ⟨6322835096373917970670445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4215223397582611980446963 6322835096373917970670445)
                    ·
                      refine ⟨2371063161140219239001417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6322835096373917970670445 2371063161140219239001417)
                      ·
                        rfl

theorem cell23_4617629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_4617629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617629 prefixEnd_4617629 := by exact prefixLift 4617629
  have htrace : WordTrace (prefixWord ++ tailWord_4617629) baseStart_4617629 baseEnd_4617629 := by
    simpa [prefixWord, tailWord_4617629, baseEnd_4617629] using wordTrace_append hprefix tailTrace_4617629
  have hstable : (prefixWord ++ tailWord_4617629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617629).length < 2 ^ (prefixWord ++ tailWord_4617629).sum := by decide
  have hdescent : baseEnd_4617629 < baseStart_4617629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617635 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 4]
def baseStart_4617635 : Nat := 118140960795 + 4617635 * 2 ^ 59
def prefixEnd_4617635 : Nat := 4983230072969 + 3 ^ 40 * 4617635 * 2
def baseEnd_4617635 : Nat := 2371066242024146215526389

theorem tailTrace_4617635 : CollatzResearch.WordTrace tailWord_4617635 prefixEnd_4617635 2371066242024146215526389 := by
  unfold tailWord_4617635
  simp only [CollatzResearch.WordTrace]
  refine ⟨168418984626104499117126359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112279323084069666078084239 168418984626104499117126359)
  ·
    refine ⟨252628476939156748675689539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168418984626104499117126359 252628476939156748675689539)
    ·
      refine ⟨378942715408735123013534309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252628476939156748675689539 378942715408735123013534309)
      ·
        refine ⟨71051759139137835565037683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 378942715408735123013534309 71051759139137835565037683)
        ·
          refine ⟨106577638708706753347556525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71051759139137835565037683 106577638708706753347556525)
          ·
            refine ⟨39966614515765032505333697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106577638708706753347556525 39966614515765032505333697)
            ·
              refine ⟨29974960886823774379000273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39966614515765032505333697 29974960886823774379000273)
              ·
                refine ⟨22481220665117830784250205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29974960886823774379000273 22481220665117830784250205)
                ·
                  refine ⟨8430457749419186544093827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22481220665117830784250205 8430457749419186544093827)
                  ·
                    refine ⟨12645686624128779816140741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8430457749419186544093827 12645686624128779816140741)
                    ·
                      refine ⟨2371066242024146215526389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12645686624128779816140741 2371066242024146215526389)
                      ·
                        rfl

theorem cell23_4617635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_4617635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617635 prefixEnd_4617635 := by exact prefixLift 4617635
  have htrace : WordTrace (prefixWord ++ tailWord_4617635) baseStart_4617635 baseEnd_4617635 := by
    simpa [prefixWord, tailWord_4617635, baseEnd_4617635] using wordTrace_append hprefix tailTrace_4617635
  have hstable : (prefixWord ++ tailWord_4617635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617635).length < 2 ^ (prefixWord ++ tailWord_4617635).sum := by decide
  have hdescent : baseEnd_4617635 < baseStart_4617635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617709 : List Nat := [1, 5, 1, 3, 2, 1, 3, 7]
def baseStart_4617709 : Nat := 118140960795 + 4617709 * 2 ^ 59
def prefixEnd_4617709 : Nat := 4983230072969 + 3 ^ 40 * 4617709 * 2
def baseEnd_4617709 : Nat := 87818675540465886148187

theorem tailTrace_4617709 : CollatzResearch.WordTrace tailWord_4617709 prefixEnd_4617709 87818675540465886148187 := by
  unfold tailWord_4617709
  simp only [CollatzResearch.WordTrace]
  refine ⟨168421683627836409755320181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112281122418557606503546787 168421683627836409755320181)
  ·
    refine ⟨15789532840109663414561267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168421683627836409755320181 15789532840109663414561267)
    ·
      refine ⟨23684299260164495121841901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15789532840109663414561267 23684299260164495121841901)
      ·
        refine ⟨8881612222561685670690713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23684299260164495121841901 8881612222561685670690713)
        ·
          refine ⟨6661209166921264253018035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8881612222561685670690713 6661209166921264253018035)
          ·
            refine ⟨9991813750381896379527053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6661209166921264253018035 9991813750381896379527053)
            ·
              refine ⟨3746930156393211142322645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9991813750381896379527053 3746930156393211142322645)
              ·
                refine ⟨87818675540465886148187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3746930156393211142322645 87818675540465886148187)
                ·
                  rfl

theorem cell23_4617709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 7].length) (baseStart_4617709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617709 prefixEnd_4617709 := by exact prefixLift 4617709
  have htrace : WordTrace (prefixWord ++ tailWord_4617709) baseStart_4617709 baseEnd_4617709 := by
    simpa [prefixWord, tailWord_4617709, baseEnd_4617709] using wordTrace_append hprefix tailTrace_4617709
  have hstable : (prefixWord ++ tailWord_4617709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617709).length < 2 ^ (prefixWord ++ tailWord_4617709).sum := by decide
  have hdescent : baseEnd_4617709 < baseStart_4617709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617759 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 1, 4, 2]
def baseStart_4617759 : Nat := 118140960795 + 4617759 * 2 ^ 59
def prefixEnd_4617759 : Nat := 4983230072969 + 3 ^ 40 * 4617759 * 2
def baseEnd_4617759 : Nat := 2371129913625303730375819

theorem tailTrace_4617759 : CollatzResearch.WordTrace tailWord_4617759 prefixEnd_4617759 2371129913625303730375819 := by
  unfold tailWord_4617759
  simp only [CollatzResearch.WordTrace]
  refine ⟨168423507277655268294640331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112282338185103512196426887 168423507277655268294640331)
  ·
    refine ⟨252635260916482902441960497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168423507277655268294640331 252635260916482902441960497)
    ·
      refine ⟨189476445687362176831470373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252635260916482902441960497 189476445687362176831470373)
      ·
        refine ⟨35526833566380408155900695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189476445687362176831470373 35526833566380408155900695)
        ·
          refine ⟨53290250349570612233851043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35526833566380408155900695 53290250349570612233851043)
          ·
            refine ⟨79935375524355918350776565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53290250349570612233851043 79935375524355918350776565)
            ·
              refine ⟨7493941455408367345385303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79935375524355918350776565 7493941455408367345385303)
              ·
                refine ⟨11240912183112551018077955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7493941455408367345385303 11240912183112551018077955)
                ·
                  refine ⟨16861368274668826527116933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11240912183112551018077955 16861368274668826527116933)
                  ·
                    refine ⟨3161506551500404973834425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16861368274668826527116933 3161506551500404973834425)
                    ·
                      refine ⟨2371129913625303730375819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3161506551500404973834425 2371129913625303730375819)
                      ·
                        rfl

theorem cell23_4617759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_4617759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617759 prefixEnd_4617759 := by exact prefixLift 4617759
  have htrace : WordTrace (prefixWord ++ tailWord_4617759) baseStart_4617759 baseEnd_4617759 := by
    simpa [prefixWord, tailWord_4617759, baseEnd_4617759] using wordTrace_append hprefix tailTrace_4617759
  have hstable : (prefixWord ++ tailWord_4617759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617759).length < 2 ^ (prefixWord ++ tailWord_4617759).sum := by decide
  have hdescent : baseEnd_4617759 < baseStart_4617759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617762 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_4617762 : Nat := 118140960795 + 4617762 * 2 ^ 59
def prefixEnd_4617762 : Nat := 4983230072969 + 3 ^ 40 * 4617762 * 2
def baseEnd_4617762 : Nat := 2371131454067267218638305

theorem tailTrace_4617762 : CollatzResearch.WordTrace tailWord_4617762 prefixEnd_4617762 2371131454067267218638305 := by
  unfold tailWord_4617762
  simp only [CollatzResearch.WordTrace]
  refine ⟨42105904174161099951749885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112282411131096266537999693 42105904174161099951749885)
  ·
    refine ⟨15789714065310412481906207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42105904174161099951749885 15789714065310412481906207)
    ·
      refine ⟨23684571097965618722859311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15789714065310412481906207 23684571097965618722859311)
      ·
        refine ⟨35526856646948428084288967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23684571097965618722859311 35526856646948428084288967)
        ·
          refine ⟨53290284970422642126433451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35526856646948428084288967 53290284970422642126433451)
          ·
            refine ⟨79935427455633963189650177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53290284970422642126433451 79935427455633963189650177)
            ·
              refine ⟨59951570591725472392237633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79935427455633963189650177 59951570591725472392237633)
              ·
                refine ⟨44963677943794104294178225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59951570591725472392237633 44963677943794104294178225)
                ·
                  refine ⟨33722758457845578220633669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44963677943794104294178225 33722758457845578220633669)
                  ·
                    refine ⟨6323017210846045916368813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33722758457845578220633669 6323017210846045916368813)
                    ·
                      refine ⟨2371131454067267218638305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6323017210846045916368813 2371131454067267218638305)
                      ·
                        rfl

theorem cell23_4617762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_4617762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617762 prefixEnd_4617762 := by exact prefixLift 4617762
  have htrace : WordTrace (prefixWord ++ tailWord_4617762) baseStart_4617762 baseEnd_4617762 := by
    simpa [prefixWord, tailWord_4617762, baseEnd_4617762] using wordTrace_append hprefix tailTrace_4617762
  have hstable : (prefixWord ++ tailWord_4617762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617762).length < 2 ^ (prefixWord ++ tailWord_4617762).sum := by decide
  have hdescent : baseEnd_4617762 < baseStart_4617762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617799 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 7]
def baseStart_4617799 : Nat := 118140960795 + 4617799 * 2 ^ 59
def prefixEnd_4617799 : Nat := 4983230072969 + 3 ^ 40 * 4617799 * 2
def baseEnd_4617799 : Nat := 263461161427942619319515

theorem tailTrace_4617799 : CollatzResearch.WordTrace tailWord_4617799 prefixEnd_4617799 263461161427942619319515 := by
  unfold tailWord_4617799
  simp only [CollatzResearch.WordTrace]
  refine ⟨168424966197510355126096451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112283310798340236750730967 168424966197510355126096451)
  ·
    refine ⟨252637449296265532689144677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168424966197510355126096451 252637449296265532689144677)
    ·
      refine ⟨47369521743049787379214627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252637449296265532689144677 47369521743049787379214627)
      ·
        refine ⟨71054282614574681068821941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47369521743049787379214627 71054282614574681068821941)
        ·
          refine ⟨6661338995116376350202057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71054282614574681068821941 6661338995116376350202057)
          ·
            refine ⟨4996004246337282262651543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6661338995116376350202057 4996004246337282262651543)
            ·
              refine ⟨7494006369505923393977315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4996004246337282262651543 7494006369505923393977315)
              ·
                refine ⟨11241009554258885090965973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7494006369505923393977315 11241009554258885090965973)
                ·
                  refine ⟨263461161427942619319515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11241009554258885090965973 263461161427942619319515)
                  ·
                    rfl

theorem cell23_4617799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 7].length) (baseStart_4617799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617799 prefixEnd_4617799 := by exact prefixLift 4617799
  have htrace : WordTrace (prefixWord ++ tailWord_4617799) baseStart_4617799 baseEnd_4617799 := by
    simpa [prefixWord, tailWord_4617799, baseEnd_4617799] using wordTrace_append hprefix tailTrace_4617799
  have hstable : (prefixWord ++ tailWord_4617799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617799).length < 2 ^ (prefixWord ++ tailWord_4617799).sum := by decide
  have hdescent : baseEnd_4617799 < baseStart_4617799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617810 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_4617810 : Nat := 118140960795 + 4617810 * 2 ^ 59
def prefixEnd_4617810 : Nat := 4983230072969 + 3 ^ 40 * 4617810 * 2
def baseEnd_4617810 : Nat := 2371156101138683030838085

theorem tailTrace_4617810 : CollatzResearch.WordTrace tailWord_4617810 prefixEnd_4617810 2371156101138683030838085 := by
  unfold tailWord_4617810
  simp only [CollatzResearch.WordTrace]
  refine ⟨42106341850117626001186721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112283578266980336003164589 42106341850117626001186721)
  ·
    refine ⟨31579756387588219500890041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42106341850117626001186721 31579756387588219500890041)
    ·
      refine ⟨23684817290691164625667531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31579756387588219500890041 23684817290691164625667531)
      ·
        refine ⟨35527225936036746938501297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23684817290691164625667531 35527225936036746938501297)
        ·
          refine ⟨26645419452027560203875973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35527225936036746938501297 26645419452027560203875973)
          ·
            refine ⟨4996016147255167538226745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26645419452027560203875973 4996016147255167538226745)
            ·
              refine ⟨3747012110441375653670059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4996016147255167538226745 3747012110441375653670059)
              ·
                refine ⟨5620518165662063480505089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3747012110441375653670059 5620518165662063480505089)
                ·
                  refine ⟨4215388624246547610378817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5620518165662063480505089 4215388624246547610378817)
                  ·
                    refine ⟨3161541468184910707784113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4215388624246547610378817 3161541468184910707784113)
                    ·
                      refine ⟨2371156101138683030838085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3161541468184910707784113 2371156101138683030838085)
                      ·
                        rfl

theorem cell23_4617810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_4617810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617810 prefixEnd_4617810 := by exact prefixLift 4617810
  have htrace : WordTrace (prefixWord ++ tailWord_4617810) baseStart_4617810 baseEnd_4617810 := by
    simpa [prefixWord, tailWord_4617810, baseEnd_4617810] using wordTrace_append hprefix tailTrace_4617810
  have hstable : (prefixWord ++ tailWord_4617810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617810).length < 2 ^ (prefixWord ++ tailWord_4617810).sum := by decide
  have hdescent : baseEnd_4617810 < baseStart_4617810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617812 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_4617812 : Nat := 118140960795 + 4617812 * 2 ^ 59
def prefixEnd_4617812 : Nat := 4983230072969 + 3 ^ 40 * 4617812 * 2
def baseEnd_4617812 : Nat := 790385709366664007671025

theorem tailTrace_4617812 : CollatzResearch.WordTrace tailWord_4617812 prefixEnd_4617812 790385709366664007671025 := by
  unfold tailWord_4617812
  simp only [CollatzResearch.WordTrace]
  refine ⟨84212720173231629173159845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112283626897642172230879793 84212720173231629173159845)
  ·
    refine ⟨15789885032480930469967471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84212720173231629173159845 15789885032480930469967471)
    ·
      refine ⟨23684827548721395704951207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15789885032480930469967471 23684827548721395704951207)
      ·
        refine ⟨35527241323082093557426811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23684827548721395704951207 35527241323082093557426811)
        ·
          refine ⟨53290861984623140336140217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35527241323082093557426811 53290861984623140336140217)
          ·
            refine ⟨39968146488467355252105163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53290861984623140336140217 39968146488467355252105163)
            ·
              refine ⟨59952219732701032878157745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39968146488467355252105163 59952219732701032878157745)
              ·
                refine ⟨44964164799525774658618309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59952219732701032878157745 44964164799525774658618309)
                ·
                  refine ⟨8430780899911082748490933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44964164799525774658618309 8430780899911082748490933)
                  ·
                    refine ⟨790385709366664007671025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8430780899911082748490933 790385709366664007671025)
                    ·
                      rfl

theorem cell23_4617812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_4617812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617812 prefixEnd_4617812 := by exact prefixLift 4617812
  have htrace : WordTrace (prefixWord ++ tailWord_4617812) baseStart_4617812 baseEnd_4617812 := by
    simpa [prefixWord, tailWord_4617812, baseEnd_4617812] using wordTrace_append hprefix tailTrace_4617812
  have hstable : (prefixWord ++ tailWord_4617812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617812).length < 2 ^ (prefixWord ++ tailWord_4617812).sum := by decide
  have hdescent : baseEnd_4617812 < baseStart_4617812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617814 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_4617814 : Nat := 118140960795 + 4617814 * 2 ^ 59
def prefixEnd_4617814 : Nat := 4983230072969 + 3 ^ 40 * 4617814 * 2
def baseEnd_4617814 : Nat := 2371158155061301015188067

theorem tailTrace_4617814 : CollatzResearch.WordTrace tailWord_4617814 prefixEnd_4617814 2371158155061301015188067 := by
  unfold tailWord_4617814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10526594580778500792993281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112283675528304008458594997 10526594580778500792993281)
  ·
    refine ⟨7894945935583875594744961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10526594580778500792993281 7894945935583875594744961)
    ·
      refine ⟨5921209451687906696058721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7894945935583875594744961 5921209451687906696058721)
      ·
        refine ⟨4440907088765930022044041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5921209451687906696058721 4440907088765930022044041)
        ·
          refine ⟨3330680316574447516533031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4440907088765930022044041 3330680316574447516533031)
          ·
            refine ⟨4996020474861671274799547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330680316574447516533031 4996020474861671274799547)
            ·
              refine ⟨7494030712292506912199321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4996020474861671274799547 7494030712292506912199321)
              ·
                refine ⟨5620523034219380184149491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7494030712292506912199321 5620523034219380184149491)
                ·
                  refine ⟨8430784551329070276224237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5620523034219380184149491 8430784551329070276224237)
                  ·
                    refine ⟨3161544206748401353584089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8430784551329070276224237 3161544206748401353584089)
                    ·
                      refine ⟨2371158155061301015188067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3161544206748401353584089 2371158155061301015188067)
                      ·
                        rfl

theorem cell23_4617814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_4617814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617814 prefixEnd_4617814 := by exact prefixLift 4617814
  have htrace : WordTrace (prefixWord ++ tailWord_4617814) baseStart_4617814 baseEnd_4617814 := by
    simpa [prefixWord, tailWord_4617814, baseEnd_4617814] using wordTrace_append hprefix tailTrace_4617814
  have hstable : (prefixWord ++ tailWord_4617814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617814).length < 2 ^ (prefixWord ++ tailWord_4617814).sum := by decide
  have hdescent : baseEnd_4617814 < baseStart_4617814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617829 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_4617829 : Nat := 118140960795 + 4617829 * 2 ^ 59
def prefixEnd_4617829 : Nat := 4983230072969 + 3 ^ 40 * 4617829 * 2
def baseEnd_4617829 : Nat := 790388619090372818833499

theorem tailTrace_4617829 : CollatzResearch.WordTrace tailWord_4617829 prefixEnd_4617829 790388619090372818833499 := by
  unfold tailWord_4617829
  simp only [CollatzResearch.WordTrace]
  refine ⟨168426060387401670249688541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112284040258267780166459027 168426060387401670249688541)
  ·
    refine ⟨63159772645275626343633203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168426060387401670249688541 63159772645275626343633203)
    ·
      refine ⟨94739658967913439515449805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63159772645275626343633203 94739658967913439515449805)
      ·
        refine ⟨35527372112967539818293677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94739658967913439515449805 35527372112967539818293677)
        ·
          refine ⟨13322764542362827431860129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35527372112967539818293677 13322764542362827431860129)
          ·
            refine ⟨9992073406772120573895097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13322764542362827431860129 9992073406772120573895097)
            ·
              refine ⟨7494055055079090430421323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9992073406772120573895097 7494055055079090430421323)
              ·
                refine ⟨11241082582618635645631985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7494055055079090430421323 11241082582618635645631985)
                ·
                  refine ⟨8430811936963976734223989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11241082582618635645631985 8430811936963976734223989)
                  ·
                    refine ⟨790388619090372818833499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8430811936963976734223989 790388619090372818833499)
                    ·
                      rfl

theorem cell23_4617829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_4617829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617829 prefixEnd_4617829 := by exact prefixLift 4617829
  have htrace : WordTrace (prefixWord ++ tailWord_4617829) baseStart_4617829 baseEnd_4617829 := by
    simpa [prefixWord, tailWord_4617829, baseEnd_4617829] using wordTrace_append hprefix tailTrace_4617829
  have hstable : (prefixWord ++ tailWord_4617829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617829).length < 2 ^ (prefixWord ++ tailWord_4617829).sum := by decide
  have hdescent : baseEnd_4617829 < baseStart_4617829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617849 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 2, 4, 2]
def baseStart_4617849 : Nat := 118140960795 + 4617849 * 2 ^ 59
def prefixEnd_4617849 : Nat := 4983230072969 + 3 ^ 40 * 4617849 * 2
def baseEnd_4617849 : Nat := 2371176126884208378250405

theorem tailTrace_4617849 : CollatzResearch.WordTrace tailWord_4617849 prefixEnd_4617849 2371176126884208378250405 := by
  unfold tailWord_4617849
  simp only [CollatzResearch.WordTrace]
  refine ⟨168426789847329213665416601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112284526564886142443611067 168426789847329213665416601)
  ·
    refine ⟨126320092385496910249062451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168426789847329213665416601 126320092385496910249062451)
    ·
      refine ⟨189480138578245365373593677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126320092385496910249062451 189480138578245365373593677)
      ·
        refine ⟨71055051966842012015097629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189480138578245365373593677 71055051966842012015097629)
        ·
          refine ⟨26645644487565754505661611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71055051966842012015097629 26645644487565754505661611)
          ·
            refine ⟨39968466731348631758492417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26645644487565754505661611 39968466731348631758492417)
            ·
              refine ⟨29976350048511473818869313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39968466731348631758492417 29976350048511473818869313)
              ·
                refine ⟨22482262536383605364151985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29976350048511473818869313 22482262536383605364151985)
                ·
                  refine ⟨16861696902287704023113989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22482262536383605364151985 16861696902287704023113989)
                  ·
                    refine ⟨3161568169178944504333873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16861696902287704023113989 3161568169178944504333873)
                    ·
                      refine ⟨2371176126884208378250405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3161568169178944504333873 2371176126884208378250405)
                      ·
                        rfl

theorem cell23_4617849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_4617849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617849 prefixEnd_4617849 := by exact prefixLift 4617849
  have htrace : WordTrace (prefixWord ++ tailWord_4617849) baseStart_4617849 baseEnd_4617849 := by
    simpa [prefixWord, tailWord_4617849, baseEnd_4617849] using wordTrace_append hprefix tailTrace_4617849
  have hstable : (prefixWord ++ tailWord_4617849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617849).length < 2 ^ (prefixWord ++ tailWord_4617849).sum := by decide
  have hdescent : baseEnd_4617849 < baseStart_4617849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617852 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_4617852 : Nat := 118140960795 + 4617852 * 2 ^ 59
def prefixEnd_4617852 : Nat := 4983230072969 + 3 ^ 40 * 4617852 * 2
def baseEnd_4617852 : Nat := 2371177667326171866512891

theorem tailTrace_4617852 : CollatzResearch.WordTrace tailWord_4617852 prefixEnd_4617852 2371177667326171866512891 := by
  unfold tailWord_4617852
  simp only [CollatzResearch.WordTrace]
  refine ⟨84213449633159172588887905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112284599510878896785183873 84213449633159172588887905)
  ·
    refine ⟨63160087224869379441665929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84213449633159172588887905 63160087224869379441665929)
    ·
      refine ⟨47370065418652034581249447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63160087224869379441665929 47370065418652034581249447)
      ·
        refine ⟨71055098127978051871874171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47370065418652034581249447 71055098127978051871874171)
        ·
          refine ⟨106582647191967077807811257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71055098127978051871874171 106582647191967077807811257)
          ·
            refine ⟨79936985393975308355858443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106582647191967077807811257 79936985393975308355858443)
            ·
              refine ⟨119905478090962962533787665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79936985393975308355858443 119905478090962962533787665)
              ·
                refine ⟨89929108568222221900340749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119905478090962962533787665 89929108568222221900340749)
                ·
                  refine ⟨33723415713083333212627781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89929108568222221900340749 33723415713083333212627781)
                  ·
                    refine ⟨6323140446203124977367709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33723415713083333212627781 6323140446203124977367709)
                    ·
                      refine ⟨2371177667326171866512891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6323140446203124977367709 2371177667326171866512891)
                      ·
                        rfl

theorem cell23_4617852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_4617852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617852 prefixEnd_4617852 := by exact prefixLift 4617852
  have htrace : WordTrace (prefixWord ++ tailWord_4617852) baseStart_4617852 baseEnd_4617852 := by
    simpa [prefixWord, tailWord_4617852, baseEnd_4617852] using wordTrace_append hprefix tailTrace_4617852
  have hstable : (prefixWord ++ tailWord_4617852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617852).length < 2 ^ (prefixWord ++ tailWord_4617852).sum := by decide
  have hdescent : baseEnd_4617852 < baseStart_4617852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617855 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 12]
def baseStart_4617855 : Nat := 118140960795 + 4617855 * 2 ^ 59
def prefixEnd_4617855 : Nat := 4983230072969 + 3 ^ 40 * 4617855 * 2
def baseEnd_4617855 : Nat := 263464356418681706086153

theorem tailTrace_4617855 : CollatzResearch.WordTrace tailWord_4617855 prefixEnd_4617855 263464356418681706086153 := by
  unfold tailWord_4617855
  simp only [CollatzResearch.WordTrace]
  refine ⟨168427008685307476690135019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112284672456871651126756679 168427008685307476690135019)
  ·
    refine ⟨252640513027961215035202529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168427008685307476690135019 252640513027961215035202529)
    ·
      refine ⟨189480384770970911276401897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252640513027961215035202529 189480384770970911276401897)
      ·
        refine ⟨142110288578228183457301423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189480384770970911276401897 142110288578228183457301423)
        ·
          refine ⟨213165432867342275185952135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142110288578228183457301423 213165432867342275185952135)
          ·
            refine ⟨319748149301013412778928203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213165432867342275185952135 319748149301013412778928203)
            ·
              refine ⟨479622223951520119168392305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319748149301013412778928203 479622223951520119168392305)
              ·
                refine ⟨359716667963640089376294229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479622223951520119168392305 359716667963640089376294229)
                ·
                  refine ⟨263464356418681706086153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 359716667963640089376294229 263464356418681706086153)
                  ·
                    rfl

theorem cell23_4617855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 12].length) (baseStart_4617855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617855 prefixEnd_4617855 := by exact prefixLift 4617855
  have htrace : WordTrace (prefixWord ++ tailWord_4617855) baseStart_4617855 baseEnd_4617855 := by
    simpa [prefixWord, tailWord_4617855, baseEnd_4617855] using wordTrace_append hprefix tailTrace_4617855
  have hstable : (prefixWord ++ tailWord_4617855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617855).length < 2 ^ (prefixWord ++ tailWord_4617855).sum := by decide
  have hdescent : baseEnd_4617855 < baseStart_4617855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617866 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2]
def baseStart_4617866 : Nat := 118140960795 + 4617866 * 2 ^ 59
def prefixEnd_4617866 : Nat := 4983230072969 + 3 ^ 40 * 4617866 * 2
def baseEnd_4617866 : Nat := 2371184856055334811737827

theorem tailTrace_4617866 : CollatzResearch.WordTrace tailWord_4617866 prefixEnd_4617866 2371184856055334811737827 := by
  unfold tailWord_4617866
  simp only [CollatzResearch.WordTrace]
  refine ⟨42106852472066906392196363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112284939925511750379190301 42106852472066906392196363)
  ·
    refine ⟨63160278708100359588294545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42106852472066906392196363 63160278708100359588294545)
    ·
      refine ⟨47370209031075269691220909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63160278708100359588294545 47370209031075269691220909)
      ·
        refine ⟨17763828386653226134207841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47370209031075269691220909 17763828386653226134207841)
        ·
          refine ⟨13322871289989919600655881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17763828386653226134207841 13322871289989919600655881)
          ·
            refine ⟨9992153467492439700491911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13322871289989919600655881 9992153467492439700491911)
            ·
              refine ⟨14988230201238659550737867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9992153467492439700491911 14988230201238659550737867)
              ·
                refine ⟨22482345301857989326106801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14988230201238659550737867 22482345301857989326106801)
                ·
                  refine ⟨16861758976393491994580101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22482345301857989326106801 16861758976393491994580101)
                  ·
                    refine ⟨3161579808073779748983769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16861758976393491994580101 3161579808073779748983769)
                    ·
                      refine ⟨2371184856055334811737827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3161579808073779748983769 2371184856055334811737827)
                      ·
                        rfl

theorem cell23_4617866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_4617866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617866 prefixEnd_4617866 := by exact prefixLift 4617866
  have htrace : WordTrace (prefixWord ++ tailWord_4617866) baseStart_4617866 baseEnd_4617866 := by
    simpa [prefixWord, tailWord_4617866, baseEnd_4617866] using wordTrace_append hprefix tailTrace_4617866
  have hstable : (prefixWord ++ tailWord_4617866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617866).length < 2 ^ (prefixWord ++ tailWord_4617866).sum := by decide
  have hdescent : baseEnd_4617866 < baseStart_4617866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617886 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_4617886 : Nat := 118140960795 + 4617886 * 2 ^ 59
def prefixEnd_4617886 : Nat := 4983230072969 + 3 ^ 40 * 4617886 * 2
def baseEnd_4617886 : Nat := 2371195125668424733487735

theorem tailTrace_4617886 : CollatzResearch.WordTrace tailWord_4617886 prefixEnd_4617886 2371195125668424733487735 := by
  unfold tailWord_4617886
  simp only [CollatzResearch.WordTrace]
  refine ⟨21053517418524396123064189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112285426232130112656342341 21053517418524396123064189)
  ·
    refine ⟨7895069031946648546149071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21053517418524396123064189 7895069031946648546149071)
    ·
      refine ⟨11842603547919972819223607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7895069031946648546149071 11842603547919972819223607)
      ·
        refine ⟨17763905321879959228835411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11842603547919972819223607 17763905321879959228835411)
        ·
          refine ⟨26645857982819938843253117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17763905321879959228835411 26645857982819938843253117)
          ·
            refine ⟨9992196743557477066219919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26645857982819938843253117 9992196743557477066219919)
            ·
              refine ⟨14988295115336215599329879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9992196743557477066219919 14988295115336215599329879)
              ·
                refine ⟨22482442673004323398994819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14988295115336215599329879 22482442673004323398994819)
                ·
                  refine ⟨33723664009506485098492229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22482442673004323398994819 33723664009506485098492229)
                  ·
                    refine ⟨6323187001782465955967293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33723664009506485098492229 6323187001782465955967293)
                    ·
                      refine ⟨2371195125668424733487735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6323187001782465955967293 2371195125668424733487735)
                      ·
                        rfl

theorem cell23_4617886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_4617886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617886 prefixEnd_4617886 := by exact prefixLift 4617886
  have htrace : WordTrace (prefixWord ++ tailWord_4617886) baseStart_4617886 baseEnd_4617886 := by
    simpa [prefixWord, tailWord_4617886, baseEnd_4617886] using wordTrace_append hprefix tailTrace_4617886
  have hstable : (prefixWord ++ tailWord_4617886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617886).length < 2 ^ (prefixWord ++ tailWord_4617886).sum := by decide
  have hdescent : baseEnd_4617886 < baseStart_4617886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617910 : List Nat := [5, 1, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4617910 : Nat := 118140960795 + 4617910 * 2 ^ 59
def prefixEnd_4617910 : Nat := 4983230072969 + 3 ^ 40 * 4617910 * 2
def baseEnd_4617910 : Nat := 790402483068044213195875

theorem tailTrace_4617910 : CollatzResearch.WordTrace tailWord_4617910 prefixEnd_4617910 790402483068044213195875 := by
  unfold tailWord_4617910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10526813418756763817711699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112286009800072147388924789 10526813418756763817711699)
  ·
    refine ⟨15790220128135145726567549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10526813418756763817711699 15790220128135145726567549)
    ·
      refine ⟨5921332548050679647462831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15790220128135145726567549 5921332548050679647462831)
      ·
        refine ⟨8881998822076019471194247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5921332548050679647462831 8881998822076019471194247)
        ·
          refine ⟨13322998233114029206791371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8881998822076019471194247 13322998233114029206791371)
          ·
            refine ⟨19984497349671043810187057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13322998233114029206791371 19984497349671043810187057)
            ·
              refine ⟨14988373012253282857640293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19984497349671043810187057 14988373012253282857640293)
              ·
                refine ⟨2810319939797490535807555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14988373012253282857640293 2810319939797490535807555)
                ·
                  refine ⟨4215479909696235803711333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810319939797490535807555 4215479909696235803711333)
                  ·
                    refine ⟨790402483068044213195875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215479909696235803711333 790402483068044213195875)
                    ·
                      rfl

theorem cell23_4617910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4617910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617910 prefixEnd_4617910 := by exact prefixLift 4617910
  have htrace : WordTrace (prefixWord ++ tailWord_4617910) baseStart_4617910 baseEnd_4617910 := by
    simpa [prefixWord, tailWord_4617910, baseEnd_4617910] using wordTrace_append hprefix tailTrace_4617910
  have hstable : (prefixWord ++ tailWord_4617910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617910).length < 2 ^ (prefixWord ++ tailWord_4617910).sum := by decide
  have hdescent : baseEnd_4617910 < baseStart_4617910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617916 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_4617916 : Nat := 118140960795 + 4617916 * 2 ^ 59
def prefixEnd_4617916 : Nat := 4983230072969 + 3 ^ 40 * 4617916 * 2
def baseEnd_4617916 : Nat := 2371210530088059616112597

theorem tailTrace_4617916 : CollatzResearch.WordTrace tailWord_4617916 prefixEnd_4617916 2371210530088059616112597 := by
  unfold tailWord_4617916
  simp only [CollatzResearch.WordTrace]
  refine ⟨84214616769043242054052801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112286155692057656072070401 84214616769043242054052801)
  ·
    refine ⟨63160962576782431540539601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84214616769043242054052801 63160962576782431540539601)
    ·
      refine ⟨47370721932586823655404701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63160962576782431540539601 47370721932586823655404701)
      ·
        refine ⟨17764020724720058870776763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47370721932586823655404701 17764020724720058870776763)
        ·
          refine ⟨26646031087080088306165145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17764020724720058870776763 26646031087080088306165145)
          ·
            refine ⟨19984523315310066229623859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26646031087080088306165145 19984523315310066229623859)
            ·
              refine ⟨29976784972965099344435789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19984523315310066229623859 29976784972965099344435789)
              ·
                refine ⟨11241294364861912254163421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29976784972965099344435789 11241294364861912254163421)
                ·
                  refine ⟨4215485386823217095311283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11241294364861912254163421 4215485386823217095311283)
                  ·
                    refine ⟨6323228080234825642966925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4215485386823217095311283 6323228080234825642966925)
                    ·
                      refine ⟨2371210530088059616112597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6323228080234825642966925 2371210530088059616112597)
                      ·
                        rfl

theorem cell23_4617916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_4617916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617916 prefixEnd_4617916 := by exact prefixLift 4617916
  have htrace : WordTrace (prefixWord ++ tailWord_4617916) baseStart_4617916 baseEnd_4617916 := by
    simpa [prefixWord, tailWord_4617916, baseEnd_4617916] using wordTrace_append hprefix tailTrace_4617916
  have hstable : (prefixWord ++ tailWord_4617916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617916).length < 2 ^ (prefixWord ++ tailWord_4617916).sum := by decide
  have hdescent : baseEnd_4617916 < baseStart_4617916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617962 : List Nat := [3, 1, 3, 1, 1, 1, 13]
def baseStart_4617962 : Nat := 118140960795 + 4617962 * 2 ^ 59
def prefixEnd_4617962 : Nat := 4983230072969 + 3 ^ 40 * 4617962 * 2
def baseEnd_4617962 : Nat := 29274495681458844890585

theorem tailTrace_4617962 : CollatzResearch.WordTrace tailWord_4617962 prefixEnd_4617962 29274495681458844890585 := by
  unfold tailWord_4617962
  simp only [CollatzResearch.WordTrace]
  refine ⟨42107727823979958491070035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112287274197279889309520093 42107727823979958491070035)
  ·
    refine ⟨63161591735969937736605053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42107727823979958491070035 63161591735969937736605053)
    ·
      refine ⟨23685596900988726651226895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63161591735969937736605053 23685596900988726651226895)
      ·
        refine ⟨35528395351483089976840343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23685596900988726651226895 35528395351483089976840343)
        ·
          refine ⟨53292593027224634965260515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35528395351483089976840343 53292593027224634965260515)
          ·
            refine ⟨79938889540836952447890773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53292593027224634965260515 79938889540836952447890773)
            ·
              refine ⟨29274495681458844890585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 79938889540836952447890773 29274495681458844890585)
              ·
                rfl

theorem cell23_4617962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 13].length) (baseStart_4617962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617962 prefixEnd_4617962 := by exact prefixLift 4617962
  have htrace : WordTrace (prefixWord ++ tailWord_4617962) baseStart_4617962 baseEnd_4617962 := by
    simpa [prefixWord, tailWord_4617962, baseEnd_4617962] using wordTrace_append hprefix tailTrace_4617962
  have hstable : (prefixWord ++ tailWord_4617962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617962).length < 2 ^ (prefixWord ++ tailWord_4617962).sum := by decide
  have hdescent : baseEnd_4617962 < baseStart_4617962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617966 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_4617966 : Nat := 118140960795 + 4617966 * 2 ^ 59
def prefixEnd_4617966 : Nat := 4983230072969 + 3 ^ 40 * 4617966 * 2
def baseEnd_4617966 : Nat := 790412068040261473495789

theorem tailTrace_4617966 : CollatzResearch.WordTrace tailWord_4617966 prefixEnd_4617966 790412068040261473495789 := by
  unfold tailWord_4617966
  simp only [CollatzResearch.WordTrace]
  refine ⟨21053882148488167830928219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112287371458603561764950501 21053882148488167830928219)
  ·
    refine ⟨31580823222732251746392329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21053882148488167830928219 31580823222732251746392329)
    ·
      refine ⟨23685617417049188809794247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31580823222732251746392329 23685617417049188809794247)
      ·
        refine ⟨35528426125573783214691371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23685617417049188809794247 35528426125573783214691371)
        ·
          refine ⟨53292639188360674822037057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35528426125573783214691371 53292639188360674822037057)
          ·
            refine ⟨39969479391270506116527793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53292639188360674822037057 39969479391270506116527793)
            ·
              refine ⟨29977109543452879587395845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39969479391270506116527793 29977109543452879587395845)
              ·
                refine ⟨5620708039397414922636721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29977109543452879587395845 5620708039397414922636721)
                ·
                  refine ⟨4215531029548061191977541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5620708039397414922636721 4215531029548061191977541)
                  ·
                    refine ⟨790412068040261473495789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215531029548061191977541 790412068040261473495789)
                    ·
                      rfl

theorem cell23_4617966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_4617966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617966 prefixEnd_4617966 := by exact prefixLift 4617966
  have htrace : WordTrace (prefixWord ++ tailWord_4617966) baseStart_4617966 baseEnd_4617966 := by
    simpa [prefixWord, tailWord_4617966, baseEnd_4617966] using wordTrace_append hprefix tailTrace_4617966
  have hstable : (prefixWord ++ tailWord_4617966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617966).length < 2 ^ (prefixWord ++ tailWord_4617966).sum := by decide
  have hdescent : baseEnd_4617966 < baseStart_4617966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4617986 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_4617986 : Nat := 118140960795 + 4617986 * 2 ^ 59
def prefixEnd_4617986 : Nat := 4983230072969 + 3 ^ 40 * 4617986 * 2
def baseEnd_4617986 : Nat := 2371246473733874342237275

theorem tailTrace_4617986 : CollatzResearch.WordTrace tailWord_4617986 prefixEnd_4617986 2371246473733874342237275 := by
  unfold tailWord_4617986
  simp only [CollatzResearch.WordTrace]
  refine ⟨42107946661958221515788453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112287857765221924042102541 42107946661958221515788453)
  ·
    refine ⟨7895239999117166534210335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42107946661958221515788453 7895239999117166534210335)
    ·
      refine ⟨11842859998675749801315503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7895239999117166534210335 11842859998675749801315503)
      ·
        refine ⟨17764289998013624701973255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11842859998675749801315503 17764289998013624701973255)
        ·
          refine ⟨26646434997020437052959883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17764289998013624701973255 26646434997020437052959883)
          ·
            refine ⟨39969652495530655579439825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26646434997020437052959883 39969652495530655579439825)
            ·
              refine ⟨29977239371647991684579869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39969652495530655579439825 29977239371647991684579869)
              ·
                refine ⟨11241464764367996881717451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29977239371647991684579869 11241464764367996881717451)
                ·
                  refine ⟨16862197146551995322576177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11241464764367996881717451 16862197146551995322576177)
                  ·
                    refine ⟨12646647859913996491932133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16862197146551995322576177 12646647859913996491932133)
                    ·
                      refine ⟨2371246473733874342237275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12646647859913996491932133 2371246473733874342237275)
                      ·
                        rfl

theorem cell23_4617986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_4617986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4617986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4617986 prefixEnd_4617986 := by exact prefixLift 4617986
  have htrace : WordTrace (prefixWord ++ tailWord_4617986) baseStart_4617986 baseEnd_4617986 := by
    simpa [prefixWord, tailWord_4617986, baseEnd_4617986] using wordTrace_append hprefix tailTrace_4617986
  have hstable : (prefixWord ++ tailWord_4617986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4617986).length < 2 ^ (prefixWord ++ tailWord_4617986).sum := by decide
  have hdescent : baseEnd_4617986 < baseStart_4617986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4617986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618024 : List Nat := [2, 1, 5, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_4618024 : Nat := 118140960795 + 4618024 * 2 ^ 59
def prefixEnd_4618024 : Nat := 4983230072969 + 3 ^ 40 * 4618024 * 2
def baseEnd_4618024 : Nat := 2371265985998745193562101

theorem tailTrace_4618024 : CollatzResearch.WordTrace tailWord_4618024 prefixEnd_4618024 2371265985998745193562101 := by
  unfold tailWord_4618024
  simp only [CollatzResearch.WordTrace]
  refine ⟨84216586310847609276518563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112288781747796812368691417 84216586310847609276518563)
  ·
    refine ⟨126324879466271413914777845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84216586310847609276518563 126324879466271413914777845)
    ·
      refine ⟨11842957449962945054510423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126324879466271413914777845 11842957449962945054510423)
      ·
        refine ⟨17764436174944417581765635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11842957449962945054510423 17764436174944417581765635)
        ·
          refine ⟨26646654262416626372648453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17764436174944417581765635 26646654262416626372648453)
          ·
            refine ⟨4996247674203117444871585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26646654262416626372648453 4996247674203117444871585)
            ·
              refine ⟨3747185755652338083653689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4996247674203117444871585 3747185755652338083653689)
              ·
                refine ⟨2810389316739253562740267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3747185755652338083653689 2810389316739253562740267)
                ·
                  refine ⟨4215583975108880344110401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810389316739253562740267 4215583975108880344110401)
                  ·
                    refine ⟨3161687981331660258082801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4215583975108880344110401 3161687981331660258082801)
                    ·
                      refine ⟨2371265985998745193562101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3161687981331660258082801 2371265985998745193562101)
                      ·
                        rfl

theorem cell23_4618024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_4618024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618024 prefixEnd_4618024 := by exact prefixLift 4618024
  have htrace : WordTrace (prefixWord ++ tailWord_4618024) baseStart_4618024 baseEnd_4618024 := by
    simpa [prefixWord, tailWord_4618024, baseEnd_4618024] using wordTrace_append hprefix tailTrace_4618024
  have hstable : (prefixWord ++ tailWord_4618024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618024).length < 2 ^ (prefixWord ++ tailWord_4618024).sum := by decide
  have hdescent : baseEnd_4618024 < baseStart_4618024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618080 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 2, 2, 2]
def baseStart_4618080 : Nat := 118140960795 + 4618080 * 2 ^ 59
def prefixEnd_4618080 : Nat := 4983230072969 + 3 ^ 40 * 4618080 * 2
def baseEnd_4618080 : Nat := 2371294740915396974461843

theorem tailTrace_4618080 : CollatzResearch.WordTrace tailWord_4618080 prefixEnd_4618080 2371294740915396974461843 := by
  unfold tailWord_4618080
  simp only [CollatzResearch.WordTrace]
  refine ⟨84217607554746170058537847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112290143406328226744717129 84217607554746170058537847)
  ·
    refine ⟨126326411332119255087806771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84217607554746170058537847 126326411332119255087806771)
    ·
      refine ⟨189489616998178882631710157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126326411332119255087806771 189489616998178882631710157)
      ·
        refine ⟨71058606374317080986891309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189489616998178882631710157 71058606374317080986891309)
        ·
          refine ⟨26646977390368905370084241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71058606374317080986891309 26646977390368905370084241)
          ·
            refine ⟨19985233042776679027563181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26646977390368905370084241 19985233042776679027563181)
            ·
              refine ⟨7494462391041254635336193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19985233042776679027563181 7494462391041254635336193)
              ·
                refine ⟨5620846793280940976502145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7494462391041254635336193 5620846793280940976502145)
                ·
                  refine ⟨4215635094960705732376609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5620846793280940976502145 4215635094960705732376609)
                  ·
                    refine ⟨3161726321220529299282457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4215635094960705732376609 3161726321220529299282457)
                    ·
                      refine ⟨2371294740915396974461843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3161726321220529299282457 2371294740915396974461843)
                      ·
                        rfl

theorem cell23_4618080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_4618080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618080 prefixEnd_4618080 := by exact prefixLift 4618080
  have htrace : WordTrace (prefixWord ++ tailWord_4618080) baseStart_4618080 baseEnd_4618080 := by
    simpa [prefixWord, tailWord_4618080, baseEnd_4618080] using wordTrace_append hprefix tailTrace_4618080
  have hstable : (prefixWord ++ tailWord_4618080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618080).length < 2 ^ (prefixWord ++ tailWord_4618080).sum := by decide
  have hdescent : baseEnd_4618080 < baseStart_4618080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618106 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2]
def baseStart_4618106 : Nat := 118140960795 + 4618106 * 2 ^ 59
def prefixEnd_4618106 : Nat := 4983230072969 + 3 ^ 40 * 4618106 * 2
def baseEnd_4618106 : Nat := 2371308091412413872736723

theorem tailTrace_4618106 : CollatzResearch.WordTrace tailWord_4618106 prefixEnd_4618106 2371308091412413872736723 := by
  unfold tailWord_4618106
  simp only [CollatzResearch.WordTrace]
  refine ⟨42109040851849536639380543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112290775604932097705014781 42109040851849536639380543)
  ·
    refine ⟨63163561277774304959070815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42109040851849536639380543 63163561277774304959070815)
    ·
      refine ⟨94745341916661457438606223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63163561277774304959070815 94745341916661457438606223)
      ·
        refine ⟨142118012874992186157909335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94745341916661457438606223 142118012874992186157909335)
        ·
          refine ⟨213177019312488279236864003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142118012874992186157909335 213177019312488279236864003)
          ·
            refine ⟨319765528968732418855296005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213177019312488279236864003 319765528968732418855296005)
            ·
              refine ⟨59956036681637328535368001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 319765528968732418855296005 59956036681637328535368001)
              ·
                refine ⟨44967027511227996401526001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59956036681637328535368001 44967027511227996401526001)
                ·
                  refine ⟨33725270633420997301144501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44967027511227996401526001 33725270633420997301144501)
                  ·
                    refine ⟨3161744121883218496982297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33725270633420997301144501 3161744121883218496982297)
                    ·
                      refine ⟨2371308091412413872736723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3161744121883218496982297 2371308091412413872736723)
                      ·
                        rfl

theorem cell23_4618106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_4618106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618106 prefixEnd_4618106 := by exact prefixLift 4618106
  have htrace : WordTrace (prefixWord ++ tailWord_4618106) baseStart_4618106 baseEnd_4618106 := by
    simpa [prefixWord, tailWord_4618106, baseEnd_4618106] using wordTrace_append hprefix tailTrace_4618106
  have hstable : (prefixWord ++ tailWord_4618106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618106).length < 2 ^ (prefixWord ++ tailWord_4618106).sum := by decide
  have hdescent : baseEnd_4618106 < baseStart_4618106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618109 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_4618109 : Nat := 118140960795 + 4618109 * 2 ^ 59
def prefixEnd_4618109 : Nat := 4983230072969 + 3 ^ 40 * 4618109 * 2
def baseEnd_4618109 : Nat := 2371309631854377360999209

theorem tailTrace_4618109 : CollatzResearch.WordTrace tailWord_4618109 prefixEnd_4618109 2371309631854377360999209 := by
  unfold tailWord_4618109
  simp only [CollatzResearch.WordTrace]
  refine ⟨168436272826387278069881381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112290848550924852046587587 168436272826387278069881381)
  ·
    refine ⟨31581801154947614638102759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168436272826387278069881381 31581801154947614638102759)
    ·
      refine ⟨47372701732421421957154139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31581801154947614638102759 47372701732421421957154139)
      ·
        refine ⟨71059052598632132935731209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47372701732421421957154139 71059052598632132935731209)
        ·
          refine ⟨53294289448974099701798407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71059052598632132935731209 53294289448974099701798407)
          ·
            refine ⟨79941434173461149552697611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53294289448974099701798407 79941434173461149552697611)
            ·
              refine ⟨119912151260191724329046417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79941434173461149552697611 119912151260191724329046417)
              ·
                refine ⟨89934113445143793246784813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119912151260191724329046417 89934113445143793246784813)
                ·
                  refine ⟨33725292541928922467544305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89934113445143793246784813 33725292541928922467544305)
                  ·
                    refine ⟨25293969406446691850658229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33725292541928922467544305 25293969406446691850658229)
                    ·
                      refine ⟨2371309631854377360999209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25293969406446691850658229 2371309631854377360999209)
                      ·
                        rfl

theorem cell23_4618109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_4618109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618109 prefixEnd_4618109 := by exact prefixLift 4618109
  have htrace : WordTrace (prefixWord ++ tailWord_4618109) baseStart_4618109 baseEnd_4618109 := by
    simpa [prefixWord, tailWord_4618109, baseEnd_4618109] using wordTrace_append hprefix tailTrace_4618109
  have hstable : (prefixWord ++ tailWord_4618109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618109).length < 2 ^ (prefixWord ++ tailWord_4618109).sum := by decide
  have hdescent : baseEnd_4618109 < baseStart_4618109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618120 : List Nat := [2, 1, 3, 3, 3, 2, 1, 3, 5]
def baseStart_4618120 : Nat := 118140960795 + 4618120 * 2 ^ 59
def prefixEnd_4618120 : Nat := 4983230072969 + 3 ^ 40 * 4618120 * 2
def baseEnd_4618120 : Nat := 263479475571286313106851

theorem tailTrace_4618120 : CollatzResearch.WordTrace tailWord_4618120 prefixEnd_4618120 263479475571286313106851 := by
  unfold tailWord_4618120
  simp only [CollatzResearch.WordTrace]
  refine ⟨84218337014673713474265907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112291116019564951299021209 84218337014673713474265907)
  ·
    refine ⟨126327505522010570211398861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84218337014673713474265907 126327505522010570211398861)
    ·
      refine ⟨47372814570753963829274573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126327505522010570211398861 47372814570753963829274573)
      ·
        refine ⟨17764805464032736435977965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47372814570753963829274573 17764805464032736435977965)
        ·
          refine ⟨6661802049012276163491737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17764805464032736435977965 6661802049012276163491737)
          ·
            refine ⟨4996351536759207122618803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6661802049012276163491737 4996351536759207122618803)
            ·
              refine ⟨7494527305138810683928205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4996351536759207122618803 7494527305138810683928205)
              ·
                refine ⟨2810447739427054006473077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7494527305138810683928205 2810447739427054006473077)
                ·
                  refine ⟨263479475571286313106851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2810447739427054006473077 263479475571286313106851)
                  ·
                    rfl

theorem cell23_4618120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 5].length) (baseStart_4618120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618120 prefixEnd_4618120 := by exact prefixLift 4618120
  have htrace : WordTrace (prefixWord ++ tailWord_4618120) baseStart_4618120 baseEnd_4618120 := by
    simpa [prefixWord, tailWord_4618120, baseEnd_4618120] using wordTrace_append hprefix tailTrace_4618120
  have hstable : (prefixWord ++ tailWord_4618120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618120).length < 2 ^ (prefixWord ++ tailWord_4618120).sum := by decide
  have hdescent : baseEnd_4618120 < baseStart_4618120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618149 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_4618149 : Nat := 118140960795 + 4618149 * 2 ^ 59
def prefixEnd_4618149 : Nat := 4983230072969 + 3 ^ 40 * 4618149 * 2
def baseEnd_4618149 : Nat := 2371330171080557204499025

theorem tailTrace_4618149 : CollatzResearch.WordTrace tailWord_4618149 prefixEnd_4618149 2371330171080557204499025 := by
  unfold tailWord_4618149
  simp only [CollatzResearch.WordTrace]
  refine ⟨168437731746242364901337501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112291821164161576600891667 168437731746242364901337501)
  ·
    refine ⟨63164149404840886838001563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168437731746242364901337501 63164149404840886838001563)
    ·
      refine ⟨94746224107261330257002345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63164149404840886838001563 94746224107261330257002345)
      ·
        refine ⟨71059668080445997692751759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94746224107261330257002345 71059668080445997692751759)
        ·
          refine ⟨106589502120668996539127639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71059668080445997692751759 106589502120668996539127639)
          ·
            refine ⟨159884253181003494808691459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106589502120668996539127639 159884253181003494808691459)
            ·
              refine ⟨239826379771505242213037189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159884253181003494808691459 239826379771505242213037189)
              ·
                refine ⟨44967446207157232914944473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239826379771505242213037189 44967446207157232914944473)
                ·
                  refine ⟨33725584655367924686208355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44967446207157232914944473 33725584655367924686208355)
                  ·
                    refine ⟨50588376983051887029312533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33725584655367924686208355 50588376983051887029312533)
                    ·
                      refine ⟨2371330171080557204499025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50588376983051887029312533 2371330171080557204499025)
                      ·
                        rfl

theorem cell23_4618149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_4618149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618149 prefixEnd_4618149 := by exact prefixLift 4618149
  have htrace : WordTrace (prefixWord ++ tailWord_4618149) baseStart_4618149 baseEnd_4618149 := by
    simpa [prefixWord, tailWord_4618149, baseEnd_4618149] using wordTrace_append hprefix tailTrace_4618149
  have hstable : (prefixWord ++ tailWord_4618149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618149).length < 2 ^ (prefixWord ++ tailWord_4618149).sum := by decide
  have hdescent : baseEnd_4618149 < baseStart_4618149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618173 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_4618173 : Nat := 118140960795 + 4618173 * 2 ^ 59
def prefixEnd_4618173 : Nat := 4983230072969 + 3 ^ 40 * 4618173 * 2
def baseEnd_4618173 : Nat := 2371342494616265110598915

theorem tailTrace_4618173 : CollatzResearch.WordTrace tailWord_4618173 prefixEnd_4618173 2371342494616265110598915 := by
  unfold tailWord_4618173
  simp only [CollatzResearch.WordTrace]
  refine ⟨168438607098155417000211173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112292404732103611333474115 168438607098155417000211173)
  ·
    refine ⟨31582238830904140687539595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168438607098155417000211173 31582238830904140687539595)
    ·
      refine ⟨47373358246356211031309393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31582238830904140687539595 47373358246356211031309393)
      ·
        refine ⟨35530018684767158273482045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47373358246356211031309393 35530018684767158273482045)
        ·
          refine ⟨13323757006787684352555767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35530018684767158273482045 13323757006787684352555767)
          ·
            refine ⟨19985635510181526528833651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13323757006787684352555767 19985635510181526528833651)
            ·
              refine ⟨29978453265272289793250477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19985635510181526528833651 29978453265272289793250477)
              ·
                refine ⟨11241919974477108672468929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29978453265272289793250477 11241919974477108672468929)
                ·
                  refine ⟨8431439980857831504351697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11241919974477108672468929 8431439980857831504351697)
                  ·
                    refine ⟨6323579985643373628263773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8431439980857831504351697 6323579985643373628263773)
                    ·
                      refine ⟨2371342494616265110598915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6323579985643373628263773 2371342494616265110598915)
                      ·
                        rfl

theorem cell23_4618173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_4618173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618173 prefixEnd_4618173 := by exact prefixLift 4618173
  have htrace : WordTrace (prefixWord ++ tailWord_4618173) baseStart_4618173 baseEnd_4618173 := by
    simpa [prefixWord, tailWord_4618173, baseEnd_4618173] using wordTrace_append hprefix tailTrace_4618173
  have hstable : (prefixWord ++ tailWord_4618173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618173).length < 2 ^ (prefixWord ++ tailWord_4618173).sum := by decide
  have hdescent : baseEnd_4618173 < baseStart_4618173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618196 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4618196 : Nat := 118140960795 + 4618196 * 2 ^ 59
def prefixEnd_4618196 : Nat := 4983230072969 + 3 ^ 40 * 4618196 * 2
def baseEnd_4618196 : Nat := 2371354304671318520611309

theorem tailTrace_4618196 : CollatzResearch.WordTrace tailWord_4618196 prefixEnd_4618196 2371354304671318520611309 := by
  unfold tailWord_4618196
  simp only [CollatzResearch.WordTrace]
  refine ⟨84219722988536045964149221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112292963984714727952198961 84219722988536045964149221)
  ·
    refine ⟨15791198060350508618277979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84219722988536045964149221 15791198060350508618277979)
    ·
      refine ⟨23686797090525762927416969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15791198060350508618277979 23686797090525762927416969)
      ·
        refine ⟨17765097817894322195562727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23686797090525762927416969 17765097817894322195562727)
        ·
          refine ⟨26647646726841483293344091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17765097817894322195562727 26647646726841483293344091)
          ·
            refine ⟨39971470090262224940016137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26647646726841483293344091 39971470090262224940016137)
            ·
              refine ⟨29978602567696668705012103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39971470090262224940016137 29978602567696668705012103)
              ·
                refine ⟨44967903851545003057518155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29978602567696668705012103 44967903851545003057518155)
                ·
                  refine ⟨67451855777317504586277233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44967903851545003057518155 67451855777317504586277233)
                  ·
                    refine ⟨50588891832988128439707925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67451855777317504586277233 50588891832988128439707925)
                    ·
                      refine ⟨2371354304671318520611309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50588891832988128439707925 2371354304671318520611309)
                      ·
                        rfl

theorem cell23_4618196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4618196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618196 prefixEnd_4618196 := by exact prefixLift 4618196
  have htrace : WordTrace (prefixWord ++ tailWord_4618196) baseStart_4618196 baseEnd_4618196 := by
    simpa [prefixWord, tailWord_4618196, baseEnd_4618196] using wordTrace_append hprefix tailTrace_4618196
  have hstable : (prefixWord ++ tailWord_4618196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618196).length < 2 ^ (prefixWord ++ tailWord_4618196).sum := by decide
  have hdescent : baseEnd_4618196 < baseStart_4618196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618197 : List Nat := [1, 3, 2, 3, 2, 1, 4, 2, 1, 4]
def baseStart_4618197 : Nat := 118140960795 + 4618197 * 2 ^ 59
def prefixEnd_4618197 : Nat := 4983230072969 + 3 ^ 40 * 4618197 * 2
def baseEnd_4618197 : Nat := 790451606050657672232935

theorem tailTrace_4618197 : CollatzResearch.WordTrace tailWord_4618197 prefixEnd_4618197 790451606050657672232935 := by
  unfold tailWord_4618197
  simp only [CollatzResearch.WordTrace]
  refine ⟨168439482450068469099084845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112292988300045646066056563 168439482450068469099084845)
  ·
    refine ⟨63164805918775675912156817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168439482450068469099084845 63164805918775675912156817)
    ·
      refine ⟨47373604439081756934117613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63164805918775675912156817 47373604439081756934117613)
      ·
        refine ⟨17765101664655658850294105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47373604439081756934117613 17765101664655658850294105)
        ·
          refine ⟨13323826248491744137720579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17765101664655658850294105 13323826248491744137720579)
          ·
            refine ⟨19985739372737616206580869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13323826248491744137720579 19985739372737616206580869)
            ·
              refine ⟨3747326132388303038733913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19985739372737616206580869 3747326132388303038733913)
              ·
                refine ⟨2810494599291227279050435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3747326132388303038733913 2810494599291227279050435)
                ·
                  refine ⟨4215741898936840918575653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810494599291227279050435 4215741898936840918575653)
                  ·
                    refine ⟨790451606050657672232935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215741898936840918575653 790451606050657672232935)
                    ·
                      rfl

theorem cell23_4618197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_4618197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618197 prefixEnd_4618197 := by exact prefixLift 4618197
  have htrace : WordTrace (prefixWord ++ tailWord_4618197) baseStart_4618197 baseEnd_4618197 := by
    simpa [prefixWord, tailWord_4618197, baseEnd_4618197] using wordTrace_append hprefix tailTrace_4618197
  have hstable : (prefixWord ++ tailWord_4618197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618197).length < 2 ^ (prefixWord ++ tailWord_4618197).sum := by decide
  have hdescent : baseEnd_4618197 < baseStart_4618197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618204 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4618204 : Nat := 118140960795 + 4618204 * 2 ^ 59
def prefixEnd_4618204 : Nat := 4983230072969 + 3 ^ 40 * 4618204 * 2
def baseEnd_4618204 : Nat := 2371358412516554489311273

theorem tailTrace_4618204 : CollatzResearch.WordTrace tailWord_4618204 prefixEnd_4618204 2371358412516554489311273 := by
  unfold tailWord_4618204
  simp only [CollatzResearch.WordTrace]
  refine ⟨84219868880521554647294833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112293158507362072863059777 84219868880521554647294833)
  ·
    refine ⟨63164901660391165985471125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84219868880521554647294833 63164901660391165985471125)
    ·
      refine ⟨2960854765330835905568959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63164901660391165985471125 2960854765330835905568959)
      ·
        refine ⟨4441282147996253858353439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960854765330835905568959 4441282147996253858353439)
        ·
          refine ⟨6661923221994380787530159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441282147996253858353439 6661923221994380787530159)
          ·
            refine ⟨9992884832991571181295239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6661923221994380787530159 9992884832991571181295239)
            ·
              refine ⟨14989327249487356771942859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9992884832991571181295239 14989327249487356771942859)
              ·
                refine ⟨22483990874231035157914289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14989327249487356771942859 22483990874231035157914289)
                ·
                  refine ⟨16862993155673276368435717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22483990874231035157914289 16862993155673276368435717)
                  ·
                    refine ⟨3161811216688739319081697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16862993155673276368435717 3161811216688739319081697)
                    ·
                      refine ⟨2371358412516554489311273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3161811216688739319081697 2371358412516554489311273)
                      ·
                        rfl

theorem cell23_4618204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4618204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618204 prefixEnd_4618204 := by exact prefixLift 4618204
  have htrace : WordTrace (prefixWord ++ tailWord_4618204) baseStart_4618204 baseEnd_4618204 := by
    simpa [prefixWord, tailWord_4618204, baseEnd_4618204] using wordTrace_append hprefix tailTrace_4618204
  have hstable : (prefixWord ++ tailWord_4618204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618204).length < 2 ^ (prefixWord ++ tailWord_4618204).sum := by decide
  have hdescent : baseEnd_4618204 < baseStart_4618204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618236 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_4618236 : Nat := 118140960795 + 4618236 * 2 ^ 59
def prefixEnd_4618236 : Nat := 4983230072969 + 3 ^ 40 * 4618236 * 2
def baseEnd_4618236 : Nat := 790458281299166121370375

theorem tailTrace_4618236 : CollatzResearch.WordTrace tailWord_4618236 prefixEnd_4618236 790458281299166121370375 := by
  unfold tailWord_4618236
  simp only [CollatzResearch.WordTrace]
  refine ⟨84220452448463589379877281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112293936597951452506503041 84220452448463589379877281)
  ·
    refine ⟨63165339336347692034907961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84220452448463589379877281 63165339336347692034907961)
    ·
      refine ⟨47374004502260769026180971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63165339336347692034907961 47374004502260769026180971)
      ·
        refine ⟨71061006753391153539271457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47374004502260769026180971 71061006753391153539271457)
        ·
          refine ⟨53295755065043365154453593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71061006753391153539271457 53295755065043365154453593)
          ·
            refine ⟨39971816298782523865840195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53295755065043365154453593 39971816298782523865840195)
            ·
              refine ⟨59957724448173785798760293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39971816298782523865840195 59957724448173785798760293)
              ·
                refine ⟨11242073334032584837267555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59957724448173785798760293 11242073334032584837267555)
                ·
                  refine ⟨16863110001048877255901333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11242073334032584837267555 16863110001048877255901333)
                  ·
                    refine ⟨790458281299166121370375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16863110001048877255901333 790458281299166121370375)
                    ·
                      rfl

theorem cell23_4618236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_4618236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618236 prefixEnd_4618236 := by exact prefixLift 4618236
  have htrace : WordTrace (prefixWord ++ tailWord_4618236) baseStart_4618236 baseEnd_4618236 := by
    simpa [prefixWord, tailWord_4618236, baseEnd_4618236] using wordTrace_append hprefix tailTrace_4618236
  have hstable : (prefixWord ++ tailWord_4618236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618236).length < 2 ^ (prefixWord ++ tailWord_4618236).sum := by decide
  have hdescent : baseEnd_4618236 < baseStart_4618236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618273 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_4618273 : Nat := 118140960795 + 4618273 * 2 ^ 59
def prefixEnd_4618273 : Nat := 4983230072969 + 3 ^ 40 * 4618273 * 2
def baseEnd_4618273 : Nat := 2371393842681714719348455

theorem tailTrace_4618273 : CollatzResearch.WordTrace tailWord_4618273 prefixEnd_4618273 2371393842681714719348455 := by
  unfold tailWord_4618273
  simp only [CollatzResearch.WordTrace]
  refine ⟨168442254397793134078851473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112294836265195422719234315 168442254397793134078851473)
  ·
    refine ⟨126331690798344850559138605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168442254397793134078851473 126331690798344850559138605)
    ·
      refine ⟨47374384049379318959676977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126331690798344850559138605 47374384049379318959676977)
      ·
        refine ⟨35530788037034489219757733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47374384049379318959676977 35530788037034489219757733)
        ·
          refine ⟨6662022756943966728704575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35530788037034489219757733 6662022756943966728704575)
          ·
            refine ⟨9993034135415950093056863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6662022756943966728704575 9993034135415950093056863)
            ·
              refine ⟨14989551203123925139585295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9993034135415950093056863 14989551203123925139585295)
              ·
                refine ⟨22484326804685887709377943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14989551203123925139585295 22484326804685887709377943)
                ·
                  refine ⟨33726490207028831564066915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22484326804685887709377943 33726490207028831564066915)
                  ·
                    refine ⟨50589735310543247346100373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33726490207028831564066915 50589735310543247346100373)
                    ·
                      refine ⟨2371393842681714719348455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50589735310543247346100373 2371393842681714719348455)
                      ·
                        rfl

theorem cell23_4618273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_4618273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618273 prefixEnd_4618273 := by exact prefixLift 4618273
  have htrace : WordTrace (prefixWord ++ tailWord_4618273) baseStart_4618273 baseEnd_4618273 := by
    simpa [prefixWord, tailWord_4618273, baseEnd_4618273] using wordTrace_append hprefix tailTrace_4618273
  have hstable : (prefixWord ++ tailWord_4618273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618273).length < 2 ^ (prefixWord ++ tailWord_4618273).sum := by decide
  have hdescent : baseEnd_4618273 < baseStart_4618273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618293 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_4618293 : Nat := 118140960795 + 4618293 * 2 ^ 59
def prefixEnd_4618293 : Nat := 4983230072969 + 3 ^ 40 * 4618293 * 2
def baseEnd_4618293 : Nat := 2371404112294804641098363

theorem tailTrace_4618293 : CollatzResearch.WordTrace tailWord_4618293 prefixEnd_4618293 2371404112294804641098363 := by
  unfold tailWord_4618293
  simp only [CollatzResearch.WordTrace]
  refine ⟨168442983857720677494579533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112295322571813784996386355 168442983857720677494579533)
  ·
    refine ⟨63166118946645254060467325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168442983857720677494579533 63166118946645254060467325)
    ·
      refine ⟨23687294604991970272675247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63166118946645254060467325 23687294604991970272675247)
      ·
        refine ⟨35530941907487955409012871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23687294604991970272675247 35530941907487955409012871)
        ·
          refine ⟨53296412861231933113519307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35530941907487955409012871 53296412861231933113519307)
          ·
            refine ⟨79944619291847899670278961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53296412861231933113519307 79944619291847899670278961)
            ·
              refine ⟨59958464468885924752709221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79944619291847899670278961 59958464468885924752709221)
              ·
                refine ⟨11242212087916110891132979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59958464468885924752709221 11242212087916110891132979)
                ·
                  refine ⟨16863318131874166336699469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11242212087916110891132979 16863318131874166336699469)
                  ·
                    refine ⟨6323744299452812376262301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16863318131874166336699469 6323744299452812376262301)
                    ·
                      refine ⟨2371404112294804641098363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6323744299452812376262301 2371404112294804641098363)
                      ·
                        rfl

theorem cell23_4618293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_4618293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618293 prefixEnd_4618293 := by exact prefixLift 4618293
  have htrace : WordTrace (prefixWord ++ tailWord_4618293) baseStart_4618293 baseEnd_4618293 := by
    simpa [prefixWord, tailWord_4618293, baseEnd_4618293] using wordTrace_append hprefix tailTrace_4618293
  have hstable : (prefixWord ++ tailWord_4618293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618293).length < 2 ^ (prefixWord ++ tailWord_4618293).sum := by decide
  have hdescent : baseEnd_4618293 < baseStart_4618293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618327 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 2, 1, 3]
def baseStart_4618327 : Nat := 118140960795 + 4618327 * 2 ^ 59
def prefixEnd_4618327 : Nat := 4983230072969 + 3 ^ 40 * 4618327 * 2
def baseEnd_4618327 : Nat := 2371421570637057508073207

theorem tailTrace_4618327 : CollatzResearch.WordTrace tailWord_4618327 prefixEnd_4618327 2371421570637057508073207 := by
  unfold tailWord_4618327
  simp only [CollatzResearch.WordTrace]
  refine ⟨168444223939597501301317235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112296149293065000867544823 168444223939597501301317235)
  ·
    refine ⟨252666335909396251951975853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168444223939597501301317235 252666335909396251951975853)
    ·
      refine ⟨94749875966023594481990945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252666335909396251951975853 94749875966023594481990945)
      ·
        refine ⟨71062406974517695861493209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94749875966023594481990945 71062406974517695861493209)
        ·
          refine ⟨53296805230888271896119907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71062406974517695861493209 53296805230888271896119907)
          ·
            refine ⟨79945207846332407844179861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53296805230888271896119907 79945207846332407844179861)
            ·
              refine ⟨3747431617796831617695931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79945207846332407844179861 3747431617796831617695931)
              ·
                refine ⟨5621147426695247426543897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3747431617796831617695931 5621147426695247426543897)
                ·
                  refine ⟨4215860570021435569907923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5621147426695247426543897 4215860570021435569907923)
                  ·
                    refine ⟨6323790855032153354861885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4215860570021435569907923 6323790855032153354861885)
                    ·
                      refine ⟨2371421570637057508073207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6323790855032153354861885 2371421570637057508073207)
                      ·
                        rfl

theorem cell23_4618327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_4618327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618327 prefixEnd_4618327 := by exact prefixLift 4618327
  have htrace : WordTrace (prefixWord ++ tailWord_4618327) baseStart_4618327 baseEnd_4618327 := by
    simpa [prefixWord, tailWord_4618327, baseEnd_4618327] using wordTrace_append hprefix tailTrace_4618327
  have hstable : (prefixWord ++ tailWord_4618327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618327).length < 2 ^ (prefixWord ++ tailWord_4618327).sum := by decide
  have hdescent : baseEnd_4618327 < baseStart_4618327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618354 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 1, 3, 2]
def baseStart_4618354 : Nat := 118140960795 + 4618354 * 2 ^ 59
def prefixEnd_4618354 : Nat := 4983230072969 + 3 ^ 40 * 4618354 * 2
def baseEnd_4618354 : Nat := 2371435434614728902435583

theorem tailTrace_4618354 : CollatzResearch.WordTrace tailWord_4618354 prefixEnd_4618354 2371435434614728902435583 := by
  unfold tailWord_4618354
  simp only [CollatzResearch.WordTrace]
  refine ⟨42111302177624921228137529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112296805806999789941700077 42111302177624921228137529)
  ·
    refine ⟨31583476633218690921103147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42111302177624921228137529 31583476633218690921103147)
    ·
      refine ⟨47375214949828036381654721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31583476633218690921103147 47375214949828036381654721)
      ·
        refine ⟨35531411212371027286241041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47375214949828036381654721 35531411212371027286241041)
        ·
          refine ⟨26648558409278270464680781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35531411212371027286241041 26648558409278270464680781)
          ·
            refine ⟨9993209403479351424255293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26648558409278270464680781 9993209403479351424255293)
            ·
              refine ⟨3747453526304756784095735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9993209403479351424255293 3747453526304756784095735)
              ·
                refine ⟨5621180289457135176143603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3747453526304756784095735 5621180289457135176143603)
                ·
                  refine ⟨8431770434185702764215405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5621180289457135176143603 8431770434185702764215405)
                  ·
                    refine ⟨3161913912819638536580777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8431770434185702764215405 3161913912819638536580777)
                    ·
                      refine ⟨2371435434614728902435583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3161913912819638536580777 2371435434614728902435583)
                      ·
                        rfl

theorem cell23_4618354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_4618354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618354 prefixEnd_4618354 := by exact prefixLift 4618354
  have htrace : WordTrace (prefixWord ++ tailWord_4618354) baseStart_4618354 baseEnd_4618354 := by
    simpa [prefixWord, tailWord_4618354, baseEnd_4618354] using wordTrace_append hprefix tailTrace_4618354
  have hstable : (prefixWord ++ tailWord_4618354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618354).length < 2 ^ (prefixWord ++ tailWord_4618354).sum := by decide
  have hdescent : baseEnd_4618354 < baseStart_4618354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618434 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_4618434 : Nat := 118140960795 + 4618434 * 2 ^ 59
def prefixEnd_4618434 : Nat := 4983230072969 + 3 ^ 40 * 4618434 * 2
def baseEnd_4618434 : Nat := 2371476513067088589435215

theorem tailTrace_4618434 : CollatzResearch.WordTrace tailWord_4618434 prefixEnd_4618434 2371476513067088589435215 := by
  unfold tailWord_4618434
  simp only [CollatzResearch.WordTrace]
  refine ⟨42112031637552464643865589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112298751033473239050308237 42112031637552464643865589)
  ·
    refine ⟨3948002966020543560362399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42112031637552464643865589 3948002966020543560362399)
    ·
      refine ⟨5922004449030815340543599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3948002966020543560362399 5922004449030815340543599)
      ·
        refine ⟨8883006673546223010815399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5922004449030815340543599 8883006673546223010815399)
        ·
          refine ⟨13324510010319334516223099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8883006673546223010815399 13324510010319334516223099)
          ·
            refine ⟨19986765015479001774334649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13324510010319334516223099 19986765015479001774334649)
            ·
              refine ⟨14990073761609251330750987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19986765015479001774334649 14990073761609251330750987)
              ·
                refine ⟨22485110642413876996126481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14990073761609251330750987 22485110642413876996126481)
                ·
                  refine ⟨16863832981810407747094861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22485110642413876996126481 16863832981810407747094861)
                  ·
                    refine ⟨6323937368178902905160573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16863832981810407747094861 6323937368178902905160573)
                    ·
                      refine ⟨2371476513067088589435215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6323937368178902905160573 2371476513067088589435215)
                      ·
                        rfl

theorem cell23_4618434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_4618434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618434 prefixEnd_4618434 := by exact prefixLift 4618434
  have htrace : WordTrace (prefixWord ++ tailWord_4618434) baseStart_4618434 baseEnd_4618434 := by
    simpa [prefixWord, tailWord_4618434, baseEnd_4618434] using wordTrace_append hprefix tailTrace_4618434
  have hstable : (prefixWord ++ tailWord_4618434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618434).length < 2 ^ (prefixWord ++ tailWord_4618434).sum := by decide
  have hdescent : baseEnd_4618434 < baseStart_4618434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618443 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 3]
def baseStart_4618443 : Nat := 118140960795 + 4618443 * 2 ^ 59
def prefixEnd_4618443 : Nat := 4983230072969 + 3 ^ 40 * 4618443 * 2
def baseEnd_4618443 : Nat := 2371481134392979054222673

theorem tailTrace_4618443 : CollatzResearch.WordTrace tailWord_4618443 prefixEnd_4618443 2371481134392979054222673 := by
  unfold tailWord_4618443
  simp only [CollatzResearch.WordTrace]
  refine ⟨168448454807177253112539983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112298969871451502075026655 168448454807177253112539983)
  ·
    refine ⟨252672682210765879668809975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168448454807177253112539983 252672682210765879668809975)
    ·
      refine ⟨379009023316148819503214963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252672682210765879668809975 379009023316148819503214963)
      ·
        refine ⟨568513534974223229254822445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379009023316148819503214963 568513534974223229254822445)
        ·
          refine ⟨213192575615333710970558417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 568513534974223229254822445 213192575615333710970558417)
          ·
            refine ⟨159894431711500283227918813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213192575615333710970558417 159894431711500283227918813)
            ·
              refine ⟨59960411891812606210469555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159894431711500283227918813 59960411891812606210469555)
              ·
                refine ⟨89940617837718909315704333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59960411891812606210469555 89940617837718909315704333)
                ·
                  refine ⟨33727731689144590993389125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89940617837718909315704333 33727731689144590993389125)
                  ·
                    refine ⟨6323949691714610811260461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33727731689144590993389125 6323949691714610811260461)
                    ·
                      refine ⟨2371481134392979054222673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6323949691714610811260461 2371481134392979054222673)
                      ·
                        rfl

theorem cell23_4618443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 3].length) (baseStart_4618443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618443 prefixEnd_4618443 := by exact prefixLift 4618443
  have htrace : WordTrace (prefixWord ++ tailWord_4618443) baseStart_4618443 baseEnd_4618443 := by
    simpa [prefixWord, tailWord_4618443, baseEnd_4618443] using wordTrace_append hprefix tailTrace_4618443
  have hstable : (prefixWord ++ tailWord_4618443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618443).length < 2 ^ (prefixWord ++ tailWord_4618443).sum := by decide
  have hdescent : baseEnd_4618443 < baseStart_4618443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618473 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 1, 7, 3]
def baseStart_4618473 : Nat := 118140960795 + 4618473 * 2 ^ 59
def prefixEnd_4618473 : Nat := 4983230072969 + 3 ^ 40 * 4618473 * 2
def baseEnd_4618473 : Nat := 2371496538812613936847535

theorem tailTrace_4618473 : CollatzResearch.WordTrace tailWord_4618473 prefixEnd_4618473 2371496538812613936847535 := by
  unfold tailWord_4618473
  simp only [CollatzResearch.WordTrace]
  refine ⟨168449548997068568236132073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112299699331379045490754715 168449548997068568236132073)
  ·
    refine ⟨126337161747801426177099055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168449548997068568236132073 126337161747801426177099055)
    ·
      refine ⟨189505742621702139265648583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126337161747801426177099055 189505742621702139265648583)
      ·
        refine ⟨284258613932553208898472875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189505742621702139265648583 284258613932553208898472875)
        ·
          refine ⟨426387920898829813347709313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284258613932553208898472875 426387920898829813347709313)
          ·
            refine ⟨319790940674122360010781985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426387920898829813347709313 319790940674122360010781985)
            ·
              refine ⟨239843205505591770008086489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319790940674122360010781985 239843205505591770008086489)
              ·
                refine ⟨179882404129193827506064867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239843205505591770008086489 179882404129193827506064867)
                ·
                  refine ⟨269823606193790741259097301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179882404129193827506064867 269823606193790741259097301)
                  ·
                    refine ⟨6323990770166970498260093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 269823606193790741259097301 6323990770166970498260093)
                    ·
                      refine ⟨2371496538812613936847535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6323990770166970498260093 2371496538812613936847535)
                      ·
                        rfl

theorem cell23_4618473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7, 3].length) (baseStart_4618473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618473 prefixEnd_4618473 := by exact prefixLift 4618473
  have htrace : WordTrace (prefixWord ++ tailWord_4618473) baseStart_4618473 baseEnd_4618473 := by
    simpa [prefixWord, tailWord_4618473, baseEnd_4618473] using wordTrace_append hprefix tailTrace_4618473
  have hstable : (prefixWord ++ tailWord_4618473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618473).length < 2 ^ (prefixWord ++ tailWord_4618473).sum := by decide
  have hdescent : baseEnd_4618473 < baseStart_4618473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618510 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_4618510 : Nat := 118140960795 + 4618510 * 2 ^ 59
def prefixEnd_4618510 : Nat := 4983230072969 + 3 ^ 40 * 4618510 * 2
def baseEnd_4618510 : Nat := 790505179198943430694955

theorem tailTrace_4618510 : CollatzResearch.WordTrace tailWord_4618510 prefixEnd_4618510 790505179198943430694955 := by
  unfold tailWord_4618510
  simp only [CollatzResearch.WordTrace]
  refine ⟨21056362312241815444403623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112300598998623015703485989 21056362312241815444403623)
  ·
    refine ⟨31584543468362723166605435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21056362312241815444403623 31584543468362723166605435)
    ·
      refine ⟨47376815202544084749908153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31584543468362723166605435 47376815202544084749908153)
      ·
        refine ⟨35532611401908063562431115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47376815202544084749908153 35532611401908063562431115)
        ·
          refine ⟨53298917102862095343646673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35532611401908063562431115 53298917102862095343646673)
          ·
            refine ⟨39974187827146571507735005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53298917102862095343646673 39974187827146571507735005)
            ·
              refine ⟨14990320435179964315400627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39974187827146571507735005 14990320435179964315400627)
              ·
                refine ⟨22485480652769946473100941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14990320435179964315400627 22485480652769946473100941)
                ·
                  refine ⟨8432055244788729927412853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22485480652769946473100941 8432055244788729927412853)
                  ·
                    refine ⟨790505179198943430694955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8432055244788729927412853 790505179198943430694955)
                    ·
                      rfl

theorem cell23_4618510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_4618510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618510 prefixEnd_4618510 := by exact prefixLift 4618510
  have htrace : WordTrace (prefixWord ++ tailWord_4618510) baseStart_4618510 baseEnd_4618510 := by
    simpa [prefixWord, tailWord_4618510, baseEnd_4618510] using wordTrace_append hprefix tailTrace_4618510
  have hstable : (prefixWord ++ tailWord_4618510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618510).length < 2 ^ (prefixWord ++ tailWord_4618510).sum := by decide
  have hdescent : baseEnd_4618510 < baseStart_4618510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618517 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 2, 3, 2]
def baseStart_4618517 : Nat := 118140960795 + 4618517 * 2 ^ 59
def prefixEnd_4618517 : Nat := 4983230072969 + 3 ^ 40 * 4618517 * 2
def baseEnd_4618517 : Nat := 2371519131961411764697333

theorem tailTrace_4618517 : CollatzResearch.WordTrace tailWord_4618517 prefixEnd_4618517 2371519131961411764697333 := by
  unfold tailWord_4618517
  simp only [CollatzResearch.WordTrace]
  refine ⟨168451153808909163750733805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112300769205939442500489203 168451153808909163750733805)
  ·
    refine ⟨63169182678340936406525177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168451153808909163750733805 63169182678340936406525177)
    ·
      refine ⟨47376887008755702304893883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63169182678340936406525177 47376887008755702304893883)
      ·
        refine ⟨71065330513133553457340825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47376887008755702304893883 71065330513133553457340825)
        ·
          refine ⟨53298997884850165093005619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71065330513133553457340825 53298997884850165093005619)
          ·
            refine ⟨79948496827275247639508429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53298997884850165093005619 79948496827275247639508429)
            ·
              refine ⟨29980686310228217864815661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79948496827275247639508429 29980686310228217864815661)
              ·
                refine ⟨11242757366335581699305873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29980686310228217864815661 11242757366335581699305873)
                ·
                  refine ⟨8432068024751686274479405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11242757366335581699305873 8432068024751686274479405)
                  ·
                    refine ⟨3162025509281882352929777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8432068024751686274479405 3162025509281882352929777)
                    ·
                      refine ⟨2371519131961411764697333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162025509281882352929777 2371519131961411764697333)
                      ·
                        rfl

theorem cell23_4618517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_4618517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618517 prefixEnd_4618517 := by exact prefixLift 4618517
  have htrace : WordTrace (prefixWord ++ tailWord_4618517) baseStart_4618517 baseEnd_4618517 := by
    simpa [prefixWord, tailWord_4618517, baseEnd_4618517] using wordTrace_append hprefix tailTrace_4618517
  have hstable : (prefixWord ++ tailWord_4618517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618517).length < 2 ^ (prefixWord ++ tailWord_4618517).sum := by decide
  have hdescent : baseEnd_4618517 < baseStart_4618517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618523 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 3, 6]
def baseStart_4618523 : Nat := 118140960795 + 4618523 * 2 ^ 59
def prefixEnd_4618523 : Nat := 4983230072969 + 3 ^ 40 * 4618523 * 2
def baseEnd_4618523 : Nat := 790507404281779580407435

theorem tailTrace_4618523 : CollatzResearch.WordTrace tailWord_4618523 prefixEnd_4618523 790507404281779580407435 := by
  unfold tailWord_4618523
  simp only [CollatzResearch.WordTrace]
  refine ⟨168451372646887426775452223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112300915097924951183634815 168451372646887426775452223)
  ·
    refine ⟨252677058970331140163178335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168451372646887426775452223 252677058970331140163178335)
    ·
      refine ⟨379015588455496710244767503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252677058970331140163178335 379015588455496710244767503)
      ·
        refine ⟨568523382683245065367151255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379015588455496710244767503 568523382683245065367151255)
        ·
          refine ⟨852785074024867598050726883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568523382683245065367151255 852785074024867598050726883)
          ·
            refine ⟨1279177611037301397076090325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852785074024867598050726883 1279177611037301397076090325)
            ·
              refine ⟨29980725258686751493970867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1279177611037301397076090325 29980725258686751493970867)
              ·
                refine ⟨44971087888030127240956301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29980725258686751493970867 44971087888030127240956301)
                ·
                  refine ⟨16864157958011297715358613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44971087888030127240956301 16864157958011297715358613)
                  ·
                    refine ⟨790507404281779580407435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16864157958011297715358613 790507404281779580407435)
                    ·
                      rfl

theorem cell23_4618523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 6].length) (baseStart_4618523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618523 prefixEnd_4618523 := by exact prefixLift 4618523
  have htrace : WordTrace (prefixWord ++ tailWord_4618523) baseStart_4618523 baseEnd_4618523 := by
    simpa [prefixWord, tailWord_4618523, baseEnd_4618523] using wordTrace_append hprefix tailTrace_4618523
  have hstable : (prefixWord ++ tailWord_4618523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618523).length < 2 ^ (prefixWord ++ tailWord_4618523).sum := by decide
  have hdescent : baseEnd_4618523 < baseStart_4618523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618524 : List Nat := [2, 2, 3, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_4618524 : Nat := 118140960795 + 4618524 * 2 ^ 59
def prefixEnd_4618524 : Nat := 4983230072969 + 3 ^ 40 * 4618524 * 2
def baseEnd_4618524 : Nat := 2371522726325993237309801

theorem tailTrace_4618524 : CollatzResearch.WordTrace tailWord_4618524 prefixEnd_4618524 2371522726325993237309801 := by
  unfold tailWord_4618524
  simp only [CollatzResearch.WordTrace]
  refine ⟨84225704559941901973119313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112300939413255869297492417 84225704559941901973119313)
  ·
    refine ⟨63169278419956426479839485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84225704559941901973119313 63169278419956426479839485)
    ·
      refine ⟨23688479407483659929939807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63169278419956426479839485 23688479407483659929939807)
      ·
        refine ⟨35532719111225489894909711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23688479407483659929939807 35532719111225489894909711)
        ·
          refine ⟨53299078666838234842364567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35532719111225489894909711 53299078666838234842364567)
          ·
            refine ⟨79948618000257352263546851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53299078666838234842364567 79948618000257352263546851)
            ·
              refine ⟨119922927000386028395320277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79948618000257352263546851 119922927000386028395320277)
              ·
                refine ⟨2810693601571547540515319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 119922927000386028395320277 2810693601571547540515319)
                ·
                  refine ⟨4216040402357321310772979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810693601571547540515319 4216040402357321310772979)
                  ·
                    refine ⟨6324060603535981966159469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4216040402357321310772979 6324060603535981966159469)
                    ·
                      refine ⟨2371522726325993237309801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6324060603535981966159469 2371522726325993237309801)
                      ·
                        rfl

theorem cell23_4618524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_4618524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618524 prefixEnd_4618524 := by exact prefixLift 4618524
  have htrace : WordTrace (prefixWord ++ tailWord_4618524) baseStart_4618524 baseEnd_4618524 := by
    simpa [prefixWord, tailWord_4618524, baseEnd_4618524] using wordTrace_append hprefix tailTrace_4618524
  have hstable : (prefixWord ++ tailWord_4618524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618524).length < 2 ^ (prefixWord ++ tailWord_4618524).sum := by decide
  have hdescent : baseEnd_4618524 < baseStart_4618524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618540 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_4618540 : Nat := 118140960795 + 4618540 * 2 ^ 59
def prefixEnd_4618540 : Nat := 4983230072969 + 3 ^ 40 * 4618540 * 2
def baseEnd_4618540 : Nat := 790510314005488391569909

theorem tailTrace_4618540 : CollatzResearch.WordTrace tailWord_4618540 prefixEnd_4618540 790510314005488391569909 := by
  unfold tailWord_4618540
  simp only [CollatzResearch.WordTrace]
  refine ⟨84225996343912919339410537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112301328458550559119214049 84225996343912919339410537)
  ·
    refine ⟨63169497257934689504557903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84225996343912919339410537 63169497257934689504557903)
    ·
      refine ⟨94754245886902034256836855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63169497257934689504557903 94754245886902034256836855)
      ·
        refine ⟨142131368830353051385255283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94754245886902034256836855 142131368830353051385255283)
        ·
          refine ⟨213197053245529577077882925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142131368830353051385255283 213197053245529577077882925)
          ·
            refine ⟨79948894967073591404206097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213197053245529577077882925 79948894967073591404206097)
            ·
              refine ⟨59961671225305193553154573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79948894967073591404206097 59961671225305193553154573)
              ·
                refine ⟨22485626709489447582432965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59961671225305193553154573 22485626709489447582432965)
                ·
                  refine ⟨4216055008029271421706181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22485626709489447582432965 4216055008029271421706181)
                  ·
                    refine ⟨790510314005488391569909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4216055008029271421706181 790510314005488391569909)
                    ·
                      rfl

theorem cell23_4618540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_4618540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618540 prefixEnd_4618540 := by exact prefixLift 4618540
  have htrace : WordTrace (prefixWord ++ tailWord_4618540) baseStart_4618540 baseEnd_4618540 := by
    simpa [prefixWord, tailWord_4618540, baseEnd_4618540] using wordTrace_append hprefix tailTrace_4618540
  have hstable : (prefixWord ++ tailWord_4618540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618540).length < 2 ^ (prefixWord ++ tailWord_4618540).sum := by decide
  have hdescent : baseEnd_4618540 < baseStart_4618540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618543 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_4618543 : Nat := 118140960795 + 4618543 * 2 ^ 59
def prefixEnd_4618543 : Nat := 4983230072969 + 3 ^ 40 * 4618543 * 2
def baseEnd_4618543 : Nat := 2371532482458428662972213

theorem tailTrace_4618543 : CollatzResearch.WordTrace tailWord_4618543 prefixEnd_4618543 2371532482458428662972213 := by
  unfold tailWord_4618543
  simp only [CollatzResearch.WordTrace]
  refine ⟨168452102106814970191180283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112301401404543313460786855 168452102106814970191180283)
  ·
    refine ⟨252678153160222455286770425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168452102106814970191180283 252678153160222455286770425)
    ·
      refine ⟨189508614870166841465077819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252678153160222455286770425 189508614870166841465077819)
      ·
        refine ⟨284262922305250262197616729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189508614870166841465077819 284262922305250262197616729)
        ·
          refine ⟨213197191728937696648212547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284262922305250262197616729 213197191728937696648212547)
          ·
            refine ⟨319795787593406544972318821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213197191728937696648212547 319795787593406544972318821)
            ·
              refine ⟨59961710173763727182309779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 319795787593406544972318821 59961710173763727182309779)
              ·
                refine ⟨89942565260645590773464669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59961710173763727182309779 89942565260645590773464669)
                ·
                  refine ⟨33728461972742096540049251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89942565260645590773464669 33728461972742096540049251)
                  ·
                    refine ⟨50592692959113144810073877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33728461972742096540049251 50592692959113144810073877)
                    ·
                      refine ⟨2371532482458428662972213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50592692959113144810073877 2371532482458428662972213)
                      ·
                        rfl

theorem cell23_4618543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_4618543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618543 prefixEnd_4618543 := by exact prefixLift 4618543
  have htrace : WordTrace (prefixWord ++ tailWord_4618543) baseStart_4618543 baseEnd_4618543 := by
    simpa [prefixWord, tailWord_4618543, baseEnd_4618543] using wordTrace_append hprefix tailTrace_4618543
  have hstable : (prefixWord ++ tailWord_4618543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618543).length < 2 ^ (prefixWord ++ tailWord_4618543).sum := by decide
  have hdescent : baseEnd_4618543 < baseStart_4618543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618567 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_4618567 : Nat := 118140960795 + 4618567 * 2 ^ 59
def prefixEnd_4618567 : Nat := 4983230072969 + 3 ^ 40 * 4618567 * 2
def baseEnd_4618567 : Nat := 2371544805994136569072103

theorem tailTrace_4618567 : CollatzResearch.WordTrace tailWord_4618567 prefixEnd_4618567 2371544805994136569072103 := by
  unfold tailWord_4618567
  simp only [CollatzResearch.WordTrace]
  refine ⟨168452977458728022290053955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112301984972485348193369303 168452977458728022290053955)
  ·
    refine ⟨252679466188092033435080933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168452977458728022290053955 252679466188092033435080933)
    ·
      refine ⟨47377399910267256269077675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252679466188092033435080933 47377399910267256269077675)
      ·
        refine ⟨71066099865400884403616513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47377399910267256269077675 71066099865400884403616513)
        ·
          refine ⟨53299574899050663302712385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71066099865400884403616513 53299574899050663302712385)
          ·
            refine ⟨39974681174287997477034289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53299574899050663302712385 39974681174287997477034289)
            ·
              refine ⟨29981010880715998107775717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39974681174287997477034289 29981010880715998107775717)
              ·
                refine ⟨5621439540134249645207947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29981010880715998107775717 5621439540134249645207947)
                ·
                  refine ⟨8432159310201374467811921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5621439540134249645207947 8432159310201374467811921)
                  ·
                    refine ⟨6324119482651030850858941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8432159310201374467811921 6324119482651030850858941)
                    ·
                      refine ⟨2371544805994136569072103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6324119482651030850858941 2371544805994136569072103)
                      ·
                        rfl

theorem cell23_4618567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_4618567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618567 prefixEnd_4618567 := by exact prefixLift 4618567
  have htrace : WordTrace (prefixWord ++ tailWord_4618567) baseStart_4618567 baseEnd_4618567 := by
    simpa [prefixWord, tailWord_4618567, baseEnd_4618567] using wordTrace_append hprefix tailTrace_4618567
  have hstable : (prefixWord ++ tailWord_4618567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618567).length < 2 ^ (prefixWord ++ tailWord_4618567).sum := by decide
  have hdescent : baseEnd_4618567 < baseStart_4618567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618581 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 1, 1, 4]
def baseStart_4618581 : Nat := 118140960795 + 4618581 * 2 ^ 59
def prefixEnd_4618581 : Nat := 4983230072969 + 3 ^ 40 * 4618581 * 2
def baseEnd_4618581 : Nat := 2371551994723299514297039

theorem tailTrace_4618581 : CollatzResearch.WordTrace tailWord_4618581 prefixEnd_4618581 2371551994723299514297039 := by
  unfold tailWord_4618581
  simp only [CollatzResearch.WordTrace]
  refine ⟨168453488080677302681063597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112302325387118201787375731 168453488080677302681063597)
  ·
    refine ⟨63170058030253988505398849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168453488080677302681063597 63170058030253988505398849)
    ·
      refine ⟨47377543522690491379049137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63170058030253988505398849 47377543522690491379049137)
      ·
        refine ⟨35533157642017868534286853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47377543522690491379049137 35533157642017868534286853)
        ·
          refine ⟨6662467057878350350178785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35533157642017868534286853 6662467057878350350178785)
          ·
            refine ⟨4996850293408762762634089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6662467057878350350178785 4996850293408762762634089)
            ·
              refine ⟨3747637720056572071975567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4996850293408762762634089 3747637720056572071975567)
              ·
                refine ⟨5621456580084858107963351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3747637720056572071975567 5621456580084858107963351)
                ·
                  refine ⟨8432184870127287161945027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5621456580084858107963351 8432184870127287161945027)
                  ·
                    refine ⟨12648277305190930742917541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8432184870127287161945027 12648277305190930742917541)
                    ·
                      refine ⟨2371551994723299514297039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12648277305190930742917541 2371551994723299514297039)
                      ·
                        rfl

theorem cell23_4618581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_4618581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618581 prefixEnd_4618581 := by exact prefixLift 4618581
  have htrace : WordTrace (prefixWord ++ tailWord_4618581) baseStart_4618581 baseEnd_4618581 := by
    simpa [prefixWord, tailWord_4618581, baseEnd_4618581] using wordTrace_append hprefix tailTrace_4618581
  have hstable : (prefixWord ++ tailWord_4618581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618581).length < 2 ^ (prefixWord ++ tailWord_4618581).sum := by decide
  have hdescent : baseEnd_4618581 < baseStart_4618581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618607 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 3, 3, 2]
def baseStart_4618607 : Nat := 118140960795 + 4618607 * 2 ^ 59
def prefixEnd_4618607 : Nat := 4983230072969 + 3 ^ 40 * 4618607 * 2
def baseEnd_4618607 : Nat := 2371565345220316412571919

theorem tailTrace_4618607 : CollatzResearch.WordTrace tailWord_4618607 prefixEnd_4618607 2371565345220316412571919 := by
  unfold tailWord_4618607
  simp only [CollatzResearch.WordTrace]
  refine ⟨168454436378583109121510075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112302957585722072747673383 168454436378583109121510075)
  ·
    refine ⟨252681654567874663682265113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168454436378583109121510075 252681654567874663682265113)
    ·
      refine ⟨189511240925905997761698835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252681654567874663682265113 189511240925905997761698835)
      ·
        refine ⟨284266861388858996642548253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189511240925905997761698835 284266861388858996642548253)
        ·
          refine ⟨106600073020822123740955595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284266861388858996642548253 106600073020822123740955595)
          ·
            refine ⟨159900109531233185611433393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106600073020822123740955595 159900109531233185611433393)
            ·
              refine ⟨119925082148424889208575045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159900109531233185611433393 119925082148424889208575045)
              ·
                refine ⟨22485952902829666726607821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119925082148424889208575045 22485952902829666726607821)
                ·
                  refine ⟨8432232338561125022477933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22485952902829666726607821 8432232338561125022477933)
                  ·
                    refine ⟨3162087126960421883429225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8432232338561125022477933 3162087126960421883429225)
                    ·
                      refine ⟨2371565345220316412571919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162087126960421883429225 2371565345220316412571919)
                      ·
                        rfl

theorem cell23_4618607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 3, 2].length) (baseStart_4618607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618607 prefixEnd_4618607 := by exact prefixLift 4618607
  have htrace : WordTrace (prefixWord ++ tailWord_4618607) baseStart_4618607 baseEnd_4618607 := by
    simpa [prefixWord, tailWord_4618607, baseEnd_4618607] using wordTrace_append hprefix tailTrace_4618607
  have hstable : (prefixWord ++ tailWord_4618607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618607).length < 2 ^ (prefixWord ++ tailWord_4618607).sum := by decide
  have hdescent : baseEnd_4618607 < baseStart_4618607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618640 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 3]
def baseStart_4618640 : Nat := 118140960795 + 4618640 * 2 ^ 59
def prefixEnd_4618640 : Nat := 4983230072969 + 3 ^ 40 * 4618640 * 2
def baseEnd_4618640 : Nat := 2371582290081914783459267

theorem tailTrace_4618640 : CollatzResearch.WordTrace tailWord_4618640 prefixEnd_4618640 2371582290081914783459267 := by
  unfold tailWord_4618640
  simp only [CollatzResearch.WordTrace]
  refine ⟨84227819993731777878730687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112303759991642370504974249 84227819993731777878730687)
  ·
    refine ⟨126341729990597666818096031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84227819993731777878730687 126341729990597666818096031)
    ·
      refine ⟨189512594985896500227144047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126341729990597666818096031 189512594985896500227144047)
      ·
        refine ⟨284268892478844750340716071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189512594985896500227144047 284268892478844750340716071)
        ·
          refine ⟨426403338718267125511074107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284268892478844750340716071 426403338718267125511074107)
          ·
            refine ⟨639605008077400688266611161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426403338718267125511074107 639605008077400688266611161)
            ·
              refine ⟨479703756058050516199958371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639605008077400688266611161 479703756058050516199958371)
              ·
                refine ⟨719555634087075774299937557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479703756058050516199958371 719555634087075774299937557)
                ·
                  refine ⟨33729170347831676920309573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 719555634087075774299937557 33729170347831676920309573)
                  ·
                    refine ⟨6324219440218439422558045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33729170347831676920309573 6324219440218439422558045)
                    ·
                      refine ⟨2371582290081914783459267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6324219440218439422558045 2371582290081914783459267)
                      ·
                        rfl

theorem cell23_4618640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 3].length) (baseStart_4618640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618640 prefixEnd_4618640 := by exact prefixLift 4618640
  have htrace : WordTrace (prefixWord ++ tailWord_4618640) baseStart_4618640 baseEnd_4618640 := by
    simpa [prefixWord, tailWord_4618640, baseEnd_4618640] using wordTrace_append hprefix tailTrace_4618640
  have hstable : (prefixWord ++ tailWord_4618640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618640).length < 2 ^ (prefixWord ++ tailWord_4618640).sum := by decide
  have hdescent : baseEnd_4618640 < baseStart_4618640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618717 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_4618717 : Nat := 118140960795 + 4618717 * 2 ^ 59
def prefixEnd_4618717 : Nat := 4983230072969 + 3 ^ 40 * 4618717 * 2
def baseEnd_4618717 : Nat := 2371621828092310982196413

theorem tailTrace_4618717 : CollatzResearch.WordTrace tailWord_4618717 prefixEnd_4618717 2371621828092310982196413 := by
  unfold tailWord_4618717
  simp only [CollatzResearch.WordTrace]
  refine ⟨168458448408184597908014405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112305632272123065272009603 168458448408184597908014405)
  ·
    refine ⟨31585959076534612107752701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168458448408184597908014405 31585959076534612107752701)
    ·
      refine ⟨11844734653700479540407263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31585959076534612107752701 11844734653700479540407263)
      ·
        refine ⟨17767101980550719310610895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11844734653700479540407263 17767101980550719310610895)
        ·
          refine ⟨26650652970826078965916343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17767101980550719310610895 26650652970826078965916343)
          ·
            refine ⟨39975979456239118448874515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26650652970826078965916343 39975979456239118448874515)
            ·
              refine ⟨59963969184358677673311773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39975979456239118448874515 59963969184358677673311773)
              ·
                refine ⟨22486488444134504127491915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59963969184358677673311773 22486488444134504127491915)
                ·
                  refine ⟨33729732666201756191237873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22486488444134504127491915 33729732666201756191237873)
                  ·
                    refine ⟨25297299499651317143428405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33729732666201756191237873 25297299499651317143428405)
                    ·
                      refine ⟨2371621828092310982196413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25297299499651317143428405 2371621828092310982196413)
                      ·
                        rfl

theorem cell23_4618717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_4618717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618717 prefixEnd_4618717 := by exact prefixLift 4618717
  have htrace : WordTrace (prefixWord ++ tailWord_4618717) baseStart_4618717 baseEnd_4618717 := by
    simpa [prefixWord, tailWord_4618717, baseEnd_4618717] using wordTrace_append hprefix tailTrace_4618717
  have hstable : (prefixWord ++ tailWord_4618717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618717).length < 2 ^ (prefixWord ++ tailWord_4618717).sum := by decide
  have hdescent : baseEnd_4618717 < baseStart_4618717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618727 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4618727 : Nat := 118140960795 + 4618727 * 2 ^ 59
def prefixEnd_4618727 : Nat := 4983230072969 + 3 ^ 40 * 4618727 * 2
def baseEnd_4618727 : Nat := 2371626962898855943071367

theorem tailTrace_4618727 : CollatzResearch.WordTrace tailWord_4618727 prefixEnd_4618727 2371626962898855943071367 := by
  unfold tailWord_4618727
  simp only [CollatzResearch.WordTrace]
  refine ⟨168458813138148369615878435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112305875425432246410585623 168458813138148369615878435)
  ·
    refine ⟨252688219707222554423817653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168458813138148369615878435 252688219707222554423817653)
    ·
      refine ⟨23689520597552114477232905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 252688219707222554423817653 23689520597552114477232905)
      ·
        refine ⟨17767140448164085857924679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23689520597552114477232905 17767140448164085857924679)
        ·
          refine ⟨26650710672246128786887019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17767140448164085857924679 26650710672246128786887019)
          ·
            refine ⟨39976066008369193180330529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26650710672246128786887019 39976066008369193180330529)
            ·
              refine ⟨29982049506276894885247897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39976066008369193180330529 29982049506276894885247897)
              ·
                refine ⟨22486537129707671163935923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29982049506276894885247897 22486537129707671163935923)
                ·
                  refine ⟨33729805694561506745903885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22486537129707671163935923 33729805694561506745903885)
                  ·
                    refine ⟨12648677135460565029713957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33729805694561506745903885 12648677135460565029713957)
                    ·
                      refine ⟨2371626962898855943071367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12648677135460565029713957 2371626962898855943071367)
                      ·
                        rfl

theorem cell23_4618727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4618727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618727 prefixEnd_4618727 := by exact prefixLift 4618727
  have htrace : WordTrace (prefixWord ++ tailWord_4618727) baseStart_4618727 baseEnd_4618727 := by
    simpa [prefixWord, tailWord_4618727, baseEnd_4618727] using wordTrace_append hprefix tailTrace_4618727
  have hstable : (prefixWord ++ tailWord_4618727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618727).length < 2 ^ (prefixWord ++ tailWord_4618727).sum := by decide
  have hdescent : baseEnd_4618727 < baseStart_4618727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618821 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 2, 3, 2]
def baseStart_4618821 : Nat := 118140960795 + 4618821 * 2 ^ 59
def prefixEnd_4618821 : Nat := 4983230072969 + 3 ^ 40 * 4618821 * 2
def baseEnd_4618821 : Nat := 2371675230080378575295935

theorem tailTrace_4618821 : CollatzResearch.WordTrace tailWord_4618821 prefixEnd_4618821 2371675230080378575295935 := by
  unfold tailWord_4618821
  simp only [CollatzResearch.WordTrace]
  refine ⟨168462241599807823669800317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112308161066538549113200211 168462241599807823669800317)
  ·
    refine ⟨63173340599927933876175119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168462241599807823669800317 63173340599927933876175119)
    ·
      refine ⟨94760010899891900814262679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63173340599927933876175119 94760010899891900814262679)
      ·
        refine ⟨142140016349837851221394019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94760010899891900814262679 142140016349837851221394019)
        ·
          refine ⟨213210024524756776832091029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142140016349837851221394019 213210024524756776832091029)
          ·
            refine ⟨9994219899597973914004267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 213210024524756776832091029 9994219899597973914004267)
            ·
              refine ⟨14991329849396960871006401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9994219899597973914004267 14991329849396960871006401)
              ·
                refine ⟨11243497387047720653254801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14991329849396960871006401 11243497387047720653254801)
                ·
                  refine ⟨8432623040285790489941101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11243497387047720653254801 8432623040285790489941101)
                  ·
                    refine ⟨3162233640107171433727913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8432623040285790489941101 3162233640107171433727913)
                    ·
                      refine ⟨2371675230080378575295935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162233640107171433727913 2371675230080378575295935)
                      ·
                        rfl

theorem cell23_4618821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_4618821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618821 prefixEnd_4618821 := by exact prefixLift 4618821
  have htrace : WordTrace (prefixWord ++ tailWord_4618821) baseStart_4618821 baseEnd_4618821 := by
    simpa [prefixWord, tailWord_4618821, baseEnd_4618821] using wordTrace_append hprefix tailTrace_4618821
  have hstable : (prefixWord ++ tailWord_4618821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618821).length < 2 ^ (prefixWord ++ tailWord_4618821).sum := by decide
  have hdescent : baseEnd_4618821 < baseStart_4618821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618822 : List Nat := [6, 1, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_4618822 : Nat := 118140960795 + 4618822 * 2 ^ 59
def prefixEnd_4618822 : Nat := 4983230072969 + 3 ^ 40 * 4618822 * 2
def baseEnd_4618822 : Nat := 790558581187011023794477

theorem tailTrace_4618822 : CollatzResearch.WordTrace tailWord_4618822 prefixEnd_4618822 790558581187011023794477 := by
  unfold tailWord_4618822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5264446189775131276268335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 112308185381869467227057813 5264446189775131276268335)
  ·
    refine ⟨7896669284662696914402503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5264446189775131276268335 7896669284662696914402503)
    ·
      refine ⟨11845003926994045371603755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7896669284662696914402503 11845003926994045371603755)
      ·
        refine ⟨17767505890491068057405633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11845003926994045371603755 17767505890491068057405633)
        ·
          refine ⟨13325629417868301043054225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17767505890491068057405633 13325629417868301043054225)
          ·
            refine ⟨9994222063401225782290669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13325629417868301043054225 9994222063401225782290669)
            ·
              refine ⟨3747833273775459668359001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9994222063401225782290669 3747833273775459668359001)
              ·
                refine ⟨2810874955331594751269251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3747833273775459668359001 2810874955331594751269251)
                ·
                  refine ⟨4216312432997392126903877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810874955331594751269251 4216312432997392126903877)
                  ·
                    refine ⟨790558581187011023794477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4216312432997392126903877 790558581187011023794477)
                    ·
                      rfl

theorem cell23_4618822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_4618822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618822 prefixEnd_4618822 := by exact prefixLift 4618822
  have htrace : WordTrace (prefixWord ++ tailWord_4618822) baseStart_4618822 baseEnd_4618822 := by
    simpa [prefixWord, tailWord_4618822, baseEnd_4618822] using wordTrace_append hprefix tailTrace_4618822
  have hstable : (prefixWord ++ tailWord_4618822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618822).length < 2 ^ (prefixWord ++ tailWord_4618822).sum := by decide
  have hdescent : baseEnd_4618822 < baseStart_4618822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618834 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_4618834 : Nat := 118140960795 + 4618834 * 2 ^ 59
def prefixEnd_4618834 : Nat := 4983230072969 + 3 ^ 40 * 4618834 * 2
def baseEnd_4618834 : Nat := 2371681905328887024433375

theorem tailTrace_4618834 : CollatzResearch.WordTrace tailWord_4618834 prefixEnd_4618834 2371681905328887024433375 := by
  unfold tailWord_4618834
  simp only [CollatzResearch.WordTrace]
  refine ⟨42115678937190181722505889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112308477165840484593349037 42115678937190181722505889)
  ·
    refine ⟨31586759202892636291879417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42115678937190181722505889 31586759202892636291879417)
    ·
      refine ⟨23690069402169477218909563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31586759202892636291879417 23690069402169477218909563)
      ·
        refine ⟨35535104103254215828364345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23690069402169477218909563 35535104103254215828364345)
        ·
          refine ⟨26651328077440661871273259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35535104103254215828364345 26651328077440661871273259)
          ·
            refine ⟨39976992116160992806909889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26651328077440661871273259 39976992116160992806909889)
            ·
              refine ⟨29982744087120744605182417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39976992116160992806909889 29982744087120744605182417)
              ·
                refine ⟨22487058065340558453886813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29982744087120744605182417 22487058065340558453886813)
                ·
                  refine ⟨8432646774502709420207555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22487058065340558453886813 8432646774502709420207555)
                  ·
                    refine ⟨12648970161754064130311333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8432646774502709420207555 12648970161754064130311333)
                    ·
                      refine ⟨2371681905328887024433375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12648970161754064130311333 2371681905328887024433375)
                      ·
                        rfl

theorem cell23_4618834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_4618834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618834 prefixEnd_4618834 := by exact prefixLift 4618834
  have htrace : WordTrace (prefixWord ++ tailWord_4618834) baseStart_4618834 baseEnd_4618834 := by
    simpa [prefixWord, tailWord_4618834, baseEnd_4618834] using wordTrace_append hprefix tailTrace_4618834
  have hstable : (prefixWord ++ tailWord_4618834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618834).length < 2 ^ (prefixWord ++ tailWord_4618834).sum := by decide
  have hdescent : baseEnd_4618834 < baseStart_4618834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618847 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_4618847 : Nat := 118140960795 + 4618847 * 2 ^ 59
def prefixEnd_4618847 : Nat := 4983230072969 + 3 ^ 40 * 4618847 * 2
def baseEnd_4618847 : Nat := 2371688580577395473570815

theorem tailTrace_4618847 : CollatzResearch.WordTrace tailWord_4618847 prefixEnd_4618847 2371688580577395473570815 := by
  unfold tailWord_4618847
  simp only [CollatzResearch.WordTrace]
  refine ⟨168463189897713630110246795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112308793265142420073497863 168463189897713630110246795)
  ·
    refine ⟨252694784846570445165370193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168463189897713630110246795 252694784846570445165370193)
    ·
      refine ⟨189521088634927833874027645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252694784846570445165370193 189521088634927833874027645)
      ·
        refine ⟨71070408238097937702760367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189521088634927833874027645 71070408238097937702760367)
        ·
          refine ⟨106605612357146906554140551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71070408238097937702760367 106605612357146906554140551)
          ·
            refine ⟨159908418535720359831210827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106605612357146906554140551 159908418535720359831210827)
            ·
              refine ⟨239862627803580539746816241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159908418535720359831210827 239862627803580539746816241)
              ·
                refine ⟨179896970852685404810112181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239862627803580539746816241 179896970852685404810112181)
                ·
                  refine ⟨16865341017439256700948017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179896970852685404810112181 16865341017439256700948017)
                  ·
                    refine ⟨12649005763079442525711013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16865341017439256700948017 12649005763079442525711013)
                    ·
                      refine ⟨2371688580577395473570815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12649005763079442525711013 2371688580577395473570815)
                      ·
                        rfl

theorem cell23_4618847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_4618847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618847 prefixEnd_4618847 := by exact prefixLift 4618847
  have htrace : WordTrace (prefixWord ++ tailWord_4618847) baseStart_4618847 baseEnd_4618847 := by
    simpa [prefixWord, tailWord_4618847, baseEnd_4618847] using wordTrace_append hprefix tailTrace_4618847
  have hstable : (prefixWord ++ tailWord_4618847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618847).length < 2 ^ (prefixWord ++ tailWord_4618847).sum := by decide
  have hdescent : baseEnd_4618847 < baseStart_4618847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618851 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 5, 2, 2]
def baseStart_4618851 : Nat := 118140960795 + 4618851 * 2 ^ 59
def prefixEnd_4618851 : Nat := 4983230072969 + 3 ^ 40 * 4618851 * 2
def baseEnd_4618851 : Nat := 2371690634500013457920797

theorem tailTrace_4618851 : CollatzResearch.WordTrace tailWord_4618851 prefixEnd_4618851 2371690634500013457920797 := by
  unfold tailWord_4618851
  simp only [CollatzResearch.WordTrace]
  refine ⟨168463335789699138793392407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112308890526466092528928271 168463335789699138793392407)
  ·
    refine ⟨252695003684548708190088611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168463335789699138793392407 252695003684548708190088611)
    ·
      refine ⟨379042505526823062285132917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252695003684548708190088611 379042505526823062285132917)
      ·
        refine ⟨35535234893139662089231211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 379042505526823062285132917 35535234893139662089231211)
        ·
          refine ⟨53302852339709493133846817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35535234893139662089231211 53302852339709493133846817)
          ·
            refine ⟨39977139254782119850385113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53302852339709493133846817 39977139254782119850385113)
            ·
              refine ⟨29982854441086589887788835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39977139254782119850385113 29982854441086589887788835)
              ·
                refine ⟨44974281661629884831683253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29982854441086589887788835 44974281661629884831683253)
                ·
                  refine ⟨4216338905777801702970305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44974281661629884831683253 4216338905777801702970305)
                  ·
                    refine ⟨3162254179333351277227729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4216338905777801702970305 3162254179333351277227729)
                    ·
                      refine ⟨2371690634500013457920797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162254179333351277227729 2371690634500013457920797)
                      ·
                        rfl

theorem cell23_4618851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_4618851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618851 prefixEnd_4618851 := by exact prefixLift 4618851
  have htrace : WordTrace (prefixWord ++ tailWord_4618851) baseStart_4618851 baseEnd_4618851 := by
    simpa [prefixWord, tailWord_4618851, baseEnd_4618851] using wordTrace_append hprefix tailTrace_4618851
  have hstable : (prefixWord ++ tailWord_4618851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618851).length < 2 ^ (prefixWord ++ tailWord_4618851).sum := by decide
  have hdescent : baseEnd_4618851 < baseStart_4618851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618885 : List Nat := [1, 3, 1, 1, 4, 3, 1, 4, 1, 2, 2]
def baseStart_4618885 : Nat := 118140960795 + 4618885 * 2 ^ 59
def prefixEnd_4618885 : Nat := 4983230072969 + 3 ^ 40 * 4618885 * 2
def baseEnd_4618885 : Nat := 2371708092842266324895641

theorem tailTrace_4618885 : CollatzResearch.WordTrace tailWord_4618885 prefixEnd_4618885 2371708092842266324895641 := by
  unfold tailWord_4618885
  simp only [CollatzResearch.WordTrace]
  refine ⟨168464575871575962600130109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112309717247717308400086739 168464575871575962600130109)
  ·
    refine ⟨63174215951840985975048791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168464575871575962600130109 63174215951840985975048791)
    ·
      refine ⟨94761323927761478962573187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63174215951840985975048791 94761323927761478962573187)
      ·
        refine ⟨142141985891642218443859781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94761323927761478962573187 142141985891642218443859781)
        ·
          refine ⟨26651622354682915958223709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142141985891642218443859781 26651622354682915958223709)
          ·
            refine ⟨9994358383006093484333891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26651622354682915958223709 9994358383006093484333891)
            ·
              refine ⟨14991537574509140226500837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9994358383006093484333891 14991537574509140226500837)
              ·
                refine ⟨2810913295220463792468907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14991537574509140226500837 2810913295220463792468907)
                ·
                  refine ⟨4216369942830695688703361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810913295220463792468907 4216369942830695688703361)
                  ·
                    refine ⟨3162277457123021766527521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4216369942830695688703361 3162277457123021766527521)
                    ·
                      refine ⟨2371708092842266324895641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162277457123021766527521 2371708092842266324895641)
                      ·
                        rfl

theorem cell23_4618885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 1, 2, 2].length) (baseStart_4618885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618885 prefixEnd_4618885 := by exact prefixLift 4618885
  have htrace : WordTrace (prefixWord ++ tailWord_4618885) baseStart_4618885 baseEnd_4618885 := by
    simpa [prefixWord, tailWord_4618885, baseEnd_4618885] using wordTrace_append hprefix tailTrace_4618885
  have hstable : (prefixWord ++ tailWord_4618885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618885).length < 2 ^ (prefixWord ++ tailWord_4618885).sum := by decide
  have hdescent : baseEnd_4618885 < baseStart_4618885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618887 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 1, 9]
def baseStart_4618887 : Nat := 118140960795 + 4618887 * 2 ^ 59
def prefixEnd_4618887 : Nat := 4983230072969 + 3 ^ 40 * 4618887 * 2
def baseEnd_4618887 : Nat := 790569706601191772356877

theorem tailTrace_4618887 : CollatzResearch.WordTrace tailWord_4618887 prefixEnd_4618887 790569706601191772356877 := by
  unfold tailWord_4618887
  simp only [CollatzResearch.WordTrace]
  refine ⟨168464648817568716941702915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112309765878379144627801943 168464648817568716941702915)
  ·
    refine ⟨252696973226353075412554373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168464648817568716941702915 252696973226353075412554373)
    ·
      refine ⟨47380682479941201639853945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252696973226353075412554373 47380682479941201639853945)
      ·
        refine ⟨35535511859955901229890459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47380682479941201639853945 35535511859955901229890459)
        ·
          refine ⟨53303267789933851844835689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35535511859955901229890459 53303267789933851844835689)
          ·
            refine ⟨39977450842450388883626767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53303267789933851844835689 39977450842450388883626767)
            ·
              refine ⟨59966176263675583325440151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39977450842450388883626767 59966176263675583325440151)
              ·
                refine ⟨89949264395513374988160227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59966176263675583325440151 89949264395513374988160227)
                ·
                  refine ⟨134923896593270062482240341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89949264395513374988160227 134923896593270062482240341)
                  ·
                    refine ⟨790569706601191772356877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 134923896593270062482240341 790569706601191772356877)
                    ·
                      rfl

theorem cell23_4618887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_4618887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618887 prefixEnd_4618887 := by exact prefixLift 4618887
  have htrace : WordTrace (prefixWord ++ tailWord_4618887) baseStart_4618887 baseEnd_4618887 := by
    simpa [prefixWord, tailWord_4618887, baseEnd_4618887] using wordTrace_append hprefix tailTrace_4618887
  have hstable : (prefixWord ++ tailWord_4618887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618887).length < 2 ^ (prefixWord ++ tailWord_4618887).sum := by decide
  have hdescent : baseEnd_4618887 < baseStart_4618887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618917 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_4618917 : Nat := 118140960795 + 4618917 * 2 ^ 59
def prefixEnd_4618917 : Nat := 4983230072969 + 3 ^ 40 * 4618917 * 2
def baseEnd_4618917 : Nat := 790574841407736733231831

theorem tailTrace_4618917 : CollatzResearch.WordTrace tailWord_4618917 prefixEnd_4618917 790574841407736733231831 := by
  unfold tailWord_4618917
  simp only [CollatzResearch.WordTrace]
  refine ⟨168465743007460032065295005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112310495338306688043530003 168465743007460032065295005)
  ·
    refine ⟨63174653627797512024485627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168465743007460032065295005 63174653627797512024485627)
    ·
      refine ⟨94761980441696268036728441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63174653627797512024485627 94761980441696268036728441)
      ·
        refine ⟨71071485331272201027546331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94761980441696268036728441 71071485331272201027546331)
        ·
          refine ⟨106607227996908301541319497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71071485331272201027546331 106607227996908301541319497)
          ·
            refine ⟨79955420997681226155989623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106607227996908301541319497 79955420997681226155989623)
            ·
              refine ⟨119933131496521839233984435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79955420997681226155989623 119933131496521839233984435)
              ·
                refine ⟨179899697244782758850976653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119933131496521839233984435 179899697244782758850976653)
                ·
                  refine ⟨67462386466793534569116245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179899697244782758850976653 67462386466793534569116245)
                  ·
                    refine ⟨790574841407736733231831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67462386466793534569116245 790574841407736733231831)
                    ·
                      rfl

theorem cell23_4618917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_4618917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618917 prefixEnd_4618917 := by exact prefixLift 4618917
  have htrace : WordTrace (prefixWord ++ tailWord_4618917) baseStart_4618917 baseEnd_4618917 := by
    simpa [prefixWord, tailWord_4618917, baseEnd_4618917] using wordTrace_append hprefix tailTrace_4618917
  have hstable : (prefixWord ++ tailWord_4618917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618917).length < 2 ^ (prefixWord ++ tailWord_4618917).sum := by decide
  have hdescent : baseEnd_4618917 < baseStart_4618917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618919 : List Nat := [1, 1, 6, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4618919 : Nat := 118140960795 + 4618919 * 2 ^ 59
def prefixEnd_4618919 : Nat := 4983230072969 + 3 ^ 40 * 4618919 * 2
def baseEnd_4618919 : Nat := 2371725551184519191870485

theorem tailTrace_4618919 : CollatzResearch.WordTrace tailWord_4618919 prefixEnd_4618919 2371725551184519191870485 := by
  unfold tailWord_4618919
  simp only [CollatzResearch.WordTrace]
  refine ⟨168465815953452786406867811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112310543968968524271245207 168465815953452786406867811)
  ·
    refine ⟨252698723930179179610301717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168465815953452786406867811 252698723930179179610301717)
    ·
      refine ⟨11845252684227149044232893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 252698723930179179610301717 11845252684227149044232893)
      ·
        refine ⟨4441969756585180891587335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11845252684227149044232893 4441969756585180891587335)
        ·
          refine ⟨6662954634877771337381003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441969756585180891587335 6662954634877771337381003)
          ·
            refine ⟨9994431952316657006071505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6662954634877771337381003 9994431952316657006071505)
            ·
              refine ⟨7495823964237492754553629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9994431952316657006071505 7495823964237492754553629)
              ·
                refine ⟨2810933986589059782957611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7495823964237492754553629 2810933986589059782957611)
                ·
                  refine ⟨4216400979883589674436417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810933986589059782957611 4216400979883589674436417)
                  ·
                    refine ⟨3162300734912692255827313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4216400979883589674436417 3162300734912692255827313)
                    ·
                      refine ⟨2371725551184519191870485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162300734912692255827313 2371725551184519191870485)
                      ·
                        rfl

theorem cell23_4618919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4618919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618919 prefixEnd_4618919 := by exact prefixLift 4618919
  have htrace : WordTrace (prefixWord ++ tailWord_4618919) baseStart_4618919 baseEnd_4618919 := by
    simpa [prefixWord, tailWord_4618919, baseEnd_4618919] using wordTrace_append hprefix tailTrace_4618919
  have hstable : (prefixWord ++ tailWord_4618919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618919).length < 2 ^ (prefixWord ++ tailWord_4618919).sum := by decide
  have hdescent : baseEnd_4618919 < baseStart_4618919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618935 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 2, 1, 3]
def baseStart_4618935 : Nat := 118140960795 + 4618935 * 2 ^ 59
def prefixEnd_4618935 : Nat := 4983230072969 + 3 ^ 40 * 4618935 * 2
def baseEnd_4618935 : Nat := 2371733766874991129270411

theorem tailTrace_4618935 : CollatzResearch.WordTrace tailWord_4618935 prefixEnd_4618935 2371733766874991129270411 := by
  unfold tailWord_4618935
  simp only [CollatzResearch.WordTrace]
  refine ⟨168466399521394821139450259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112310933014263214092966839 168466399521394821139450259)
  ·
    refine ⟨252699599282092231709175389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168466399521394821139450259 252699599282092231709175389)
    ·
      refine ⟨94762349730784586890940771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252699599282092231709175389 94762349730784586890940771)
      ·
        refine ⟨142143524596176880336411157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94762349730784586890940771 142143524596176880336411157)
        ·
          refine ⟨6662977715445791265769273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 142143524596176880336411157 6662977715445791265769273)
          ·
            refine ⟨4997233286584343449326955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6662977715445791265769273 4997233286584343449326955)
            ·
              refine ⟨7495849929876515173990433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4997233286584343449326955 7495849929876515173990433)
              ·
                refine ⟨5621887447407386380492825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7495849929876515173990433 5621887447407386380492825)
                ·
                  refine ⟨4216415585555539785369619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5621887447407386380492825 4216415585555539785369619)
                  ·
                    refine ⟨6324623378333309678054429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4216415585555539785369619 6324623378333309678054429)
                    ·
                      refine ⟨2371733766874991129270411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6324623378333309678054429 2371733766874991129270411)
                      ·
                        rfl

theorem cell23_4618935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_4618935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618935 prefixEnd_4618935 := by exact prefixLift 4618935
  have htrace : WordTrace (prefixWord ++ tailWord_4618935) baseStart_4618935 baseEnd_4618935 := by
    simpa [prefixWord, tailWord_4618935, baseEnd_4618935] using wordTrace_append hprefix tailTrace_4618935
  have hstable : (prefixWord ++ tailWord_4618935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618935).length < 2 ^ (prefixWord ++ tailWord_4618935).sum := by decide
  have hdescent : baseEnd_4618935 < baseStart_4618935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4618958 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2]
def baseStart_4618958 : Nat := 118140960795 + 4618958 * 2 ^ 59
def prefixEnd_4618958 : Nat := 4983230072969 + 3 ^ 40 * 4618958 * 2
def baseEnd_4618958 : Nat := 2371745576930044539282805

theorem tailTrace_4618958 : CollatzResearch.WordTrace tailWord_4618958 prefixEnd_4618958 2371745576930044539282805 := by
  unfold tailWord_4618958
  simp only [CollatzResearch.WordTrace]
  refine ⟨21058404800038937008442191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112311492266874330711691685 21058404800038937008442191)
  ·
    refine ⟨31587607200058405512663287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21058404800038937008442191 31587607200058405512663287)
    ·
      refine ⟨47381410800087608268994931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31587607200058405512663287 47381410800087608268994931)
      ·
        refine ⟨71072116200131412403492397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47381410800087608268994931 71072116200131412403492397)
        ·
          refine ⟨26652043575049279651309649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71072116200131412403492397 26652043575049279651309649)
          ·
            refine ⟨19989032681286959738482237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26652043575049279651309649 19989032681286959738482237)
            ·
              refine ⟨7495887255482609901930839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19989032681286959738482237 7495887255482609901930839)
              ·
                refine ⟨11243830883223914852896259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7495887255482609901930839 11243830883223914852896259)
                ·
                  refine ⟨16865746324835872279344389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11243830883223914852896259 16865746324835872279344389)
                  ·
                    refine ⟨3162327435906726052377073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16865746324835872279344389 3162327435906726052377073)
                    ·
                      refine ⟨2371745576930044539282805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162327435906726052377073 2371745576930044539282805)
                      ·
                        rfl

theorem cell23_4618958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_4618958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4618958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4618958 prefixEnd_4618958 := by exact prefixLift 4618958
  have htrace : WordTrace (prefixWord ++ tailWord_4618958) baseStart_4618958 baseEnd_4618958 := by
    simpa [prefixWord, tailWord_4618958, baseEnd_4618958] using wordTrace_append hprefix tailTrace_4618958
  have hstable : (prefixWord ++ tailWord_4618958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4618958).length < 2 ^ (prefixWord ++ tailWord_4618958).sum := by decide
  have hdescent : baseEnd_4618958 < baseStart_4618958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4618958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619004 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_4619004 : Nat := 118140960795 + 4619004 * 2 ^ 59
def prefixEnd_4619004 : Nat := 4983230072969 + 3 ^ 40 * 4619004 * 2
def baseEnd_4619004 : Nat := 2371769197040151359307593

theorem tailTrace_4619004 : CollatzResearch.WordTrace tailWord_4619004 prefixEnd_4619004 2371769197040151359307593 := by
  unfold tailWord_4619004
  simp only [CollatzResearch.WordTrace]
  refine ⟨84234458079072422961856033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112312610772096563949141377 84234458079072422961856033)
  ·
    refine ⟨63175843559304317221392025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84234458079072422961856033 63175843559304317221392025)
    ·
      refine ⟨47381882669478237916044019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63175843559304317221392025 47381882669478237916044019)
      ·
        refine ⟨71072824004217356874066029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47381882669478237916044019 71072824004217356874066029)
        ·
          refine ⟨26652309001581508827774761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71072824004217356874066029 26652309001581508827774761)
          ·
            refine ⟨19989231751186131620831071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26652309001581508827774761 19989231751186131620831071)
            ·
              refine ⟨29983847626779197431246607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19989231751186131620831071 29983847626779197431246607)
              ·
                refine ⟨44975771440168796146869911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29983847626779197431246607 44975771440168796146869911)
                ·
                  refine ⟨67463657160253194220304867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44975771440168796146869911 67463657160253194220304867)
                  ·
                    refine ⟨101195485740379791330457301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67463657160253194220304867 101195485740379791330457301)
                    ·
                      refine ⟨2371769197040151359307593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101195485740379791330457301 2371769197040151359307593)
                      ·
                        rfl

theorem cell23_4619004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_4619004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619004 prefixEnd_4619004 := by exact prefixLift 4619004
  have htrace : WordTrace (prefixWord ++ tailWord_4619004) baseStart_4619004 baseEnd_4619004 := by
    simpa [prefixWord, tailWord_4619004, baseEnd_4619004] using wordTrace_append hprefix tailTrace_4619004
  have hstable : (prefixWord ++ tailWord_4619004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619004).length < 2 ^ (prefixWord ++ tailWord_4619004).sum := by decide
  have hdescent : baseEnd_4619004 < baseStart_4619004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619048 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_4619048 : Nat := 118140960795 + 4619048 * 2 ^ 59
def prefixEnd_4619048 : Nat := 4983230072969 + 3 ^ 40 * 4619048 * 2
def baseEnd_4619048 : Nat := 2371791790188949187157391

theorem tailTrace_4619048 : CollatzResearch.WordTrace tailWord_4619048 prefixEnd_4619048 2371791790188949187157391 := by
  unfold tailWord_4619048
  simp only [CollatzResearch.WordTrace]
  refine ⟨84235260484992720719156899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112313680646656960958875865 84235260484992720719156899)
  ·
    refine ⟨126352890727489081078735349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84235260484992720719156899 126352890727489081078735349)
    ·
      refine ⟨11845583505702101351131439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126352890727489081078735349 11845583505702101351131439)
      ·
        refine ⟨17768375258553152026697159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11845583505702101351131439 17768375258553152026697159)
        ·
          refine ⟨26652562887829728040045739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17768375258553152026697159 26652562887829728040045739)
          ·
            refine ⟨39978844331744592060068609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26652562887829728040045739 39978844331744592060068609)
            ·
              refine ⟨29984133248808444045051457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39978844331744592060068609 29984133248808444045051457)
              ·
                refine ⟨22488099936606333033788593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29984133248808444045051457 22488099936606333033788593)
                ·
                  refine ⟨16866074952454749775341445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22488099936606333033788593 16866074952454749775341445)
                  ·
                    refine ⟨3162389053585265582876521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16866074952454749775341445 3162389053585265582876521)
                    ·
                      refine ⟨2371791790188949187157391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162389053585265582876521 2371791790188949187157391)
                      ·
                        rfl

theorem cell23_4619048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_4619048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619048 prefixEnd_4619048 := by exact prefixLift 4619048
  have htrace : WordTrace (prefixWord ++ tailWord_4619048) baseStart_4619048 baseEnd_4619048 := by
    simpa [prefixWord, tailWord_4619048, baseEnd_4619048] using wordTrace_append hprefix tailTrace_4619048
  have hstable : (prefixWord ++ tailWord_4619048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619048).length < 2 ^ (prefixWord ++ tailWord_4619048).sum := by decide
  have hdescent : baseEnd_4619048 < baseStart_4619048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619071 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 6]
def baseStart_4619071 : Nat := 118140960795 + 4619071 * 2 ^ 59
def prefixEnd_4619071 : Nat := 4983230072969 + 3 ^ 40 * 4619071 * 2
def baseEnd_4619071 : Nat := 263533733360444733018865

theorem tailTrace_4619071 : CollatzResearch.WordTrace tailWord_4619071 prefixEnd_4619071 263533733360444733018865 := by
  unfold tailWord_4619071
  simp only [CollatzResearch.WordTrace]
  refine ⟨168471359848902116366401067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112314239899268077577600711 168471359848902116366401067)
  ·
    refine ⟨252707039773353174549601601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168471359848902116366401067 252707039773353174549601601)
    ·
      refine ⟨189530279830014880912201201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252707039773353174549601601 189530279830014880912201201)
      ·
        refine ⟨142147709872511160684150901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189530279830014880912201201 142147709872511160684150901)
        ·
          refine ⟨13326347800547921314139147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142147709872511160684150901 13326347800547921314139147)
          ·
            refine ⟨19989521700821881971208721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13326347800547921314139147 19989521700821881971208721)
            ·
              refine ⟨14992141275616411478406541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19989521700821881971208721 14992141275616411478406541)
              ·
                refine ⟨5622052978356154304402453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14992141275616411478406541 5622052978356154304402453)
                ·
                  refine ⟨263533733360444733018865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5622052978356154304402453 263533733360444733018865)
                  ·
                    rfl

theorem cell23_4619071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 6].length) (baseStart_4619071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619071 prefixEnd_4619071 := by exact prefixLift 4619071
  have htrace : WordTrace (prefixWord ++ tailWord_4619071) baseStart_4619071 baseEnd_4619071 := by
    simpa [prefixWord, tailWord_4619071, baseEnd_4619071] using wordTrace_append hprefix tailTrace_4619071
  have hstable : (prefixWord ++ tailWord_4619071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619071).length < 2 ^ (prefixWord ++ tailWord_4619071).sum := by decide
  have hdescent : baseEnd_4619071 < baseStart_4619071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619085 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_4619085 : Nat := 118140960795 + 4619085 * 2 ^ 59
def prefixEnd_4619085 : Nat := 4983230072969 + 3 ^ 40 * 4619085 * 2
def baseEnd_4619085 : Nat := 2371810788973165542394721

theorem tailTrace_4619085 : CollatzResearch.WordTrace tailWord_4619085 prefixEnd_4619085 2371810788973165542394721 := by
  unfold tailWord_4619085
  simp only [CollatzResearch.WordTrace]
  refine ⟨168471870470851396757410709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112314580313900931171607139 168471870470851396757410709)
  ·
    refine ⟨7897118928321159223003627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 168471870470851396757410709 7897118928321159223003627)
    ·
      refine ⟨11845678392481738834505441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7897118928321159223003627 11845678392481738834505441)
      ·
        refine ⟨8884258794361304125879081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11845678392481738834505441 8884258794361304125879081)
        ·
          refine ⟨6663194095770978094409311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8884258794361304125879081 6663194095770978094409311)
          ·
            refine ⟨9994791143656467141613967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6663194095770978094409311 9994791143656467141613967)
            ·
              refine ⟨14992186715484700712420951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9994791143656467141613967 14992186715484700712420951)
              ·
                refine ⟨22488280073227051068631427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14992186715484700712420951 22488280073227051068631427)
                ·
                  refine ⟨33732420109840576602947141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22488280073227051068631427 33732420109840576602947141)
                  ·
                    refine ⟨6324828770595108113052589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33732420109840576602947141 6324828770595108113052589)
                    ·
                      refine ⟨2371810788973165542394721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6324828770595108113052589 2371810788973165542394721)
                      ·
                        rfl

theorem cell23_4619085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_4619085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619085 prefixEnd_4619085 := by exact prefixLift 4619085
  have htrace : WordTrace (prefixWord ++ tailWord_4619085) baseStart_4619085 baseEnd_4619085 := by
    simpa [prefixWord, tailWord_4619085, baseEnd_4619085] using wordTrace_append hprefix tailTrace_4619085
  have hstable : (prefixWord ++ tailWord_4619085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619085).length < 2 ^ (prefixWord ++ tailWord_4619085).sum := by decide
  have hdescent : baseEnd_4619085 < baseStart_4619085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619092 : List Nat := [2, 4, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_4619092 : Nat := 118140960795 + 4619092 * 2 ^ 59
def prefixEnd_4619092 : Nat := 4983230072969 + 3 ^ 40 * 4619092 * 2
def baseEnd_4619092 : Nat := 790604794445915671669063

theorem tailTrace_4619092 : CollatzResearch.WordTrace tailWord_4619092 prefixEnd_4619092 790604794445915671669063 := by
  unfold tailWord_4619092
  simp only [CollatzResearch.WordTrace]
  refine ⟨84236062890913018476457765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112314750521217357968610353 84236062890913018476457765)
  ·
    refine ⟨15794261792046190964335831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84236062890913018476457765 15794261792046190964335831)
    ·
      refine ⟨23691392688069286446503747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15794261792046190964335831 23691392688069286446503747)
      ·
        refine ⟨35537089032103929669755621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23691392688069286446503747 35537089032103929669755621)
        ·
          refine ⟨6663204193519486813079179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35537089032103929669755621 6663204193519486813079179)
          ·
            refine ⟨9994806290279230219618769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6663204193519486813079179 9994806290279230219618769)
            ·
              refine ⟨7496104717709422664714077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9994806290279230219618769 7496104717709422664714077)
              ·
                refine ⟨2811039269141033499267779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7496104717709422664714077 2811039269141033499267779)
                ·
                  refine ⟨4216558903711550248901669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811039269141033499267779 4216558903711550248901669)
                  ·
                    refine ⟨790604794445915671669063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4216558903711550248901669 790604794445915671669063)
                    ·
                      rfl

theorem cell23_4619092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_4619092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619092 prefixEnd_4619092 := by exact prefixLift 4619092
  have htrace : WordTrace (prefixWord ++ tailWord_4619092) baseStart_4619092 baseEnd_4619092 := by
    simpa [prefixWord, tailWord_4619092, baseEnd_4619092] using wordTrace_append hprefix tailTrace_4619092
  have hstable : (prefixWord ++ tailWord_4619092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619092).length < 2 ^ (prefixWord ++ tailWord_4619092).sum := by decide
  have hdescent : baseEnd_4619092 < baseStart_4619092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619115 : List Nat := [1, 1, 1, 1, 2, 2, 6, 4, 1, 1, 3]
def baseStart_4619115 : Nat := 118140960795 + 4619115 * 2 ^ 59
def prefixEnd_4619115 : Nat := 4983230072969 + 3 ^ 40 * 4619115 * 2
def baseEnd_4619115 : Nat := 2371826193392800425019583

theorem tailTrace_4619115 : CollatzResearch.WordTrace tailWord_4619115 prefixEnd_4619115 2371826193392800425019583 := by
  unfold tailWord_4619115
  simp only [CollatzResearch.WordTrace]
  refine ⟨168472964660742711881002799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112315309773828474587335199 168472964660742711881002799)
  ·
    refine ⟨252709446991114067821504199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168472964660742711881002799 252709446991114067821504199)
    ·
      refine ⟨379064170486671101732256299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252709446991114067821504199 379064170486671101732256299)
      ·
        refine ⟨568596255730006652598384449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379064170486671101732256299 568596255730006652598384449)
        ·
          refine ⟨426447191797504989448788337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 568596255730006652598384449 426447191797504989448788337)
          ·
            refine ⟨319835393848128742086591253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426447191797504989448788337 319835393848128742086591253)
            ·
              refine ⟨14992284086631034785308965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 319835393848128742086591253 14992284086631034785308965)
              ·
                refine ⟨2811053266243319022245431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14992284086631034785308965 2811053266243319022245431)
                ·
                  refine ⟨4216579899364978533368147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811053266243319022245431 4216579899364978533368147)
                  ·
                    refine ⟨6324869849047467800052221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4216579899364978533368147 6324869849047467800052221)
                    ·
                      refine ⟨2371826193392800425019583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6324869849047467800052221 2371826193392800425019583)
                      ·
                        rfl

theorem cell23_4619115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 1, 1, 3].length) (baseStart_4619115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619115 prefixEnd_4619115 := by exact prefixLift 4619115
  have htrace : WordTrace (prefixWord ++ tailWord_4619115) baseStart_4619115 baseEnd_4619115 := by
    simpa [prefixWord, tailWord_4619115, baseEnd_4619115] using wordTrace_append hprefix tailTrace_4619115
  have hstable : (prefixWord ++ tailWord_4619115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619115).length < 2 ^ (prefixWord ++ tailWord_4619115).sum := by decide
  have hdescent : baseEnd_4619115 < baseStart_4619115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619131 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 1, 6]
def baseStart_4619131 : Nat := 118140960795 + 4619131 * 2 ^ 59
def prefixEnd_4619131 : Nat := 4983230072969 + 3 ^ 40 * 4619131 * 2
def baseEnd_4619131 : Nat := 790611469694424120806503

theorem tailTrace_4619131 : CollatzResearch.WordTrace tailWord_4619131 prefixEnd_4619131 790611469694424120806503 := by
  unfold tailWord_4619131
  simp only [CollatzResearch.WordTrace]
  refine ⟨168473548228684746613585247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112315698819123164409056831 168473548228684746613585247)
  ·
    refine ⟨252710322343027119920377871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168473548228684746613585247 252710322343027119920377871)
    ·
      refine ⟨379065483514540679880566807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252710322343027119920377871 379065483514540679880566807)
      ·
        refine ⟨568598225271811019820850211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379065483514540679880566807 568598225271811019820850211)
        ·
          refine ⟨852897337907716529731275317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568598225271811019820850211 852897337907716529731275317)
          ·
            refine ⟨79959125428848424662307061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 852897337907716529731275317 79959125428848424662307061)
            ·
              refine ⟨7496168008954539812091287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79959125428848424662307061 7496168008954539812091287)
              ·
                refine ⟨11244252013431809718136931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7496168008954539812091287 11244252013431809718136931)
                ·
                  refine ⟨16866378020147714577205397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11244252013431809718136931 16866378020147714577205397)
                  ·
                    refine ⟨790611469694424120806503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16866378020147714577205397 790611469694424120806503)
                    ·
                      rfl

theorem cell23_4619131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 6].length) (baseStart_4619131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619131 prefixEnd_4619131 := by exact prefixLift 4619131
  have htrace : WordTrace (prefixWord ++ tailWord_4619131) baseStart_4619131 baseEnd_4619131 := by
    simpa [prefixWord, tailWord_4619131, baseEnd_4619131] using wordTrace_append hprefix tailTrace_4619131
  have hstable : (prefixWord ++ tailWord_4619131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619131).length < 2 ^ (prefixWord ++ tailWord_4619131).sum := by decide
  have hdescent : baseEnd_4619131 < baseStart_4619131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619261 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_4619261 : Nat := 118140960795 + 4619261 * 2 ^ 59
def prefixEnd_4619261 : Nat := 4983230072969 + 3 ^ 40 * 4619261 * 2
def baseEnd_4619261 : Nat := 2371901161568356853793911

theorem tailTrace_4619261 : CollatzResearch.WordTrace tailWord_4619261 prefixEnd_4619261 2371901161568356853793911 := by
  unfold tailWord_4619261
  simp only [CollatzResearch.WordTrace]
  refine ⟨168478289718213778815817637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112318859812142519210545091 168478289718213778815817637)
  ·
    refine ⟨31589679322165083527965807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168478289718213778815817637 31589679322165083527965807)
    ·
      refine ⟨47384518983247625291948711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31589679322165083527965807 47384518983247625291948711)
      ·
        refine ⟨71076778474871437937923067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47384518983247625291948711 71076778474871437937923067)
        ·
          refine ⟨106615167712307156906884601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71076778474871437937923067 106615167712307156906884601)
          ·
            refine ⟨79961375784230367680163451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106615167712307156906884601 79961375784230367680163451)
            ·
              refine ⟨119942063676345551520245177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79961375784230367680163451 119942063676345551520245177)
              ·
                refine ⟨89956547757259163640183883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119942063676345551520245177 89956547757259163640183883)
                ·
                  refine ⟨134934821635888745460275825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89956547757259163640183883 134934821635888745460275825)
                  ·
                    refine ⟨101201116226916559095206869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134934821635888745460275825 101201116226916559095206869)
                    ·
                      refine ⟨2371901161568356853793911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101201116226916559095206869 2371901161568356853793911)
                      ·
                        rfl

theorem cell23_4619261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_4619261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619261 prefixEnd_4619261 := by exact prefixLift 4619261
  have htrace : WordTrace (prefixWord ++ tailWord_4619261) baseStart_4619261 baseEnd_4619261 := by
    simpa [prefixWord, tailWord_4619261, baseEnd_4619261] using wordTrace_append hprefix tailTrace_4619261
  have hstable : (prefixWord ++ tailWord_4619261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619261).length < 2 ^ (prefixWord ++ tailWord_4619261).sum := by decide
  have hdescent : baseEnd_4619261 < baseStart_4619261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619266 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4619266 : Nat := 118140960795 + 4619266 * 2 ^ 59
def prefixEnd_4619266 : Nat := 4983230072969 + 3 ^ 40 * 4619266 * 2
def baseEnd_4619266 : Nat := 2371903728971629334231389

theorem tailTrace_4619266 : CollatzResearch.WordTrace tailWord_4619266 prefixEnd_4619266 2371903728971629334231389 := by
  unfold tailWord_4619266
  simp only [CollatzResearch.WordTrace]
  refine ⟨42119618020798916167437413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112318981388797109779833101 42119618020798916167437413)
  ·
    refine ⟨7897428378899796781394515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42119618020798916167437413 7897428378899796781394515)
    ·
      refine ⟨11846142568349695172091773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7897428378899796781394515 11846142568349695172091773)
      ·
        refine ⟨4442303463131135689534415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11846142568349695172091773 4442303463131135689534415)
        ·
          refine ⟨6663455194696703534301623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4442303463131135689534415 6663455194696703534301623)
          ·
            refine ⟨9995182792045055301452435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6663455194696703534301623 9995182792045055301452435)
            ·
              refine ⟨14992774188067582952178653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9995182792045055301452435 14992774188067582952178653)
              ·
                refine ⟨5622290320525343607066995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14992774188067582952178653 5622290320525343607066995)
                ·
                  refine ⟨8433435480788015410600493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5622290320525343607066995 8433435480788015410600493)
                  ·
                    refine ⟨3162538305295505778975185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8433435480788015410600493 3162538305295505778975185)
                    ·
                      refine ⟨2371903728971629334231389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162538305295505778975185 2371903728971629334231389)
                      ·
                        rfl

theorem cell23_4619266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4619266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619266 prefixEnd_4619266 := by exact prefixLift 4619266
  have htrace : WordTrace (prefixWord ++ tailWord_4619266) baseStart_4619266 baseEnd_4619266 := by
    simpa [prefixWord, tailWord_4619266, baseEnd_4619266] using wordTrace_append hprefix tailTrace_4619266
  have hstable : (prefixWord ++ tailWord_4619266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619266).length < 2 ^ (prefixWord ++ tailWord_4619266).sum := by decide
  have hdescent : baseEnd_4619266 < baseStart_4619266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619285 : List Nat := [1, 3, 2, 1, 4, 1, 2, 4, 5]
def baseStart_4619285 : Nat := 118140960795 + 4619285 * 2 ^ 59
def prefixEnd_4619285 : Nat := 4983230072969 + 3 ^ 40 * 4619285 * 2
def baseEnd_4619285 : Nat := 263545942789340528877089

theorem tailTrace_4619285 : CollatzResearch.WordTrace tailWord_4619285 prefixEnd_4619285 263545942789340528877089 := by
  unfold tailWord_4619285
  simp only [CollatzResearch.WordTrace]
  refine ⟨168479165070126830914691309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112319443380084553943127539 168479165070126830914691309)
  ·
    refine ⟨63179686901297561593009241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168479165070126830914691309 63179686901297561593009241)
    ·
      refine ⟨47384765175973171194756931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63179686901297561593009241 47384765175973171194756931)
      ·
        refine ⟨71077147763959756792135397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47384765175973171194756931 71077147763959756792135397)
        ·
          refine ⟨13326965205742454398525387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71077147763959756792135397 13326965205742454398525387)
          ·
            refine ⟨19990447808613681597788081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13326965205742454398525387 19990447808613681597788081)
            ·
              refine ⟨14992835856460261198341061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19990447808613681597788081 14992835856460261198341061)
              ·
                refine ⟨2811156723086298974688949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14992835856460261198341061 2811156723086298974688949)
                ·
                  refine ⟨263545942789340528877089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2811156723086298974688949 263545942789340528877089)
                  ·
                    rfl

theorem cell23_4619285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_4619285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619285 prefixEnd_4619285 := by exact prefixLift 4619285
  have htrace : WordTrace (prefixWord ++ tailWord_4619285) baseStart_4619285 baseEnd_4619285 := by
    simpa [prefixWord, tailWord_4619285, baseEnd_4619285] using wordTrace_append hprefix tailTrace_4619285
  have hstable : (prefixWord ++ tailWord_4619285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619285).length < 2 ^ (prefixWord ++ tailWord_4619285).sum := by decide
  have hdescent : baseEnd_4619285 < baseStart_4619285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619291 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 5]
def baseStart_4619291 : Nat := 118140960795 + 4619291 * 2 ^ 59
def prefixEnd_4619291 : Nat := 4983230072969 + 3 ^ 40 * 4619291 * 2
def baseEnd_4619291 : Nat := 2371916565987991736418773

theorem tailTrace_4619291 : CollatzResearch.WordTrace tailWord_4619291 prefixEnd_4619291 2371916565987991736418773 := by
  unfold tailWord_4619291
  simp only [CollatzResearch.WordTrace]
  refine ⟨168479383908105093939409727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112319589272070062626273151 168479383908105093939409727)
  ·
    refine ⟨252719075862157640909114591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168479383908105093939409727 252719075862157640909114591)
    ·
      refine ⟨379078613793236461363671887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252719075862157640909114591 379078613793236461363671887)
      ·
        refine ⟨568617920689854692045507831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379078613793236461363671887 568617920689854692045507831)
        ·
          refine ⟨852926881034782038068261747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568617920689854692045507831 852926881034782038068261747)
          ·
            refine ⟨1279390321552173057102392621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852926881034782038068261747 1279390321552173057102392621)
            ·
              refine ⟨479771370582064896413397233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1279390321552173057102392621 479771370582064896413397233)
              ·
                refine ⟨359828527936548672310047925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479771370582064896413397233 359828527936548672310047925)
                ·
                  refine ⟨33733924494051438029066993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 359828527936548672310047925 33733924494051438029066993)
                  ·
                    refine ⟨25300443370538578521800245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33733924494051438029066993 25300443370538578521800245)
                    ·
                      refine ⟨2371916565987991736418773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25300443370538578521800245 2371916565987991736418773)
                      ·
                        rfl

theorem cell23_4619291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_4619291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619291 prefixEnd_4619291 := by exact prefixLift 4619291
  have htrace : WordTrace (prefixWord ++ tailWord_4619291) baseStart_4619291 baseEnd_4619291 := by
    simpa [prefixWord, tailWord_4619291, baseEnd_4619291] using wordTrace_append hprefix tailTrace_4619291
  have hstable : (prefixWord ++ tailWord_4619291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619291).length < 2 ^ (prefixWord ++ tailWord_4619291).sum := by decide
  have hdescent : baseEnd_4619291 < baseStart_4619291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619296 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4619296 : Nat := 118140960795 + 4619296 * 2 ^ 59
def prefixEnd_4619296 : Nat := 4983230072969 + 3 ^ 40 * 4619296 * 2
def baseEnd_4619296 : Nat := 2371919133391264216856251

theorem tailTrace_4619296 : CollatzResearch.WordTrace tailWord_4619296 prefixEnd_4619296 2371919133391264216856251 := by
  unfold tailWord_4619296
  simp only [CollatzResearch.WordTrace]
  refine ⟨84239783136543489896670871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112319710848724653195561161 84239783136543489896670871)
  ·
    refine ⟨126359674704815234845006307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84239783136543489896670871 126359674704815234845006307)
    ·
      refine ⟨189539512057222852267509461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126359674704815234845006307 189539512057222852267509461)
      ·
        refine ⟨4442332313841160600019753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 189539512057222852267509461 4442332313841160600019753)
        ·
          refine ⟨3331749235380870450014815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4442332313841160600019753 3331749235380870450014815)
          ·
            refine ⟨4997623853071305675022223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3331749235380870450014815 4997623853071305675022223)
            ·
              refine ⟨7496435779606958512533335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4997623853071305675022223 7496435779606958512533335)
              ·
                refine ⟨11244653669410437768800003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7496435779606958512533335 11244653669410437768800003)
                ·
                  refine ⟨16866980504115656653200005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11244653669410437768800003 16866980504115656653200005)
                  ·
                    refine ⟨3162558844521685622475001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16866980504115656653200005 3162558844521685622475001)
                    ·
                      refine ⟨2371919133391264216856251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3162558844521685622475001 2371919133391264216856251)
                      ·
                        rfl

theorem cell23_4619296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4619296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619296 prefixEnd_4619296 := by exact prefixLift 4619296
  have htrace : WordTrace (prefixWord ++ tailWord_4619296) baseStart_4619296 baseEnd_4619296 := by
    simpa [prefixWord, tailWord_4619296, baseEnd_4619296] using wordTrace_append hprefix tailTrace_4619296
  have hstable : (prefixWord ++ tailWord_4619296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619296).length < 2 ^ (prefixWord ++ tailWord_4619296).sum := by decide
  have hdescent : baseEnd_4619296 < baseStart_4619296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619298 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_4619298 : Nat := 118140960795 + 4619298 * 2 ^ 59
def prefixEnd_4619298 : Nat := 4983230072969 + 3 ^ 40 * 4619298 * 2
def baseEnd_4619298 : Nat := 790640053450857736343747

theorem tailTrace_4619298 : CollatzResearch.WordTrace tailWord_4619298 prefixEnd_4619298 790640053450857736343747 := by
  unfold tailWord_4619298
  simp only [CollatzResearch.WordTrace]
  refine ⟨42119909804769933533728637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112319759479386489423276365 42119909804769933533728637)
  ·
    refine ⟨15794966176788725075148239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42119909804769933533728637 15794966176788725075148239)
    ·
      refine ⟨23692449265183087612722359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15794966176788725075148239 23692449265183087612722359)
      ·
        refine ⟨35538673897774631419083539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23692449265183087612722359 35538673897774631419083539)
        ·
          refine ⟨53308010846661947128625309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35538673897774631419083539 53308010846661947128625309)
          ·
            refine ⟨19990504067498230173234491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53308010846661947128625309 19990504067498230173234491)
            ·
              refine ⟨29985756101247345259851737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19990504067498230173234491 29985756101247345259851737)
              ·
                refine ⟨22489317075935508944888803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29985756101247345259851737 22489317075935508944888803)
                ·
                  refine ⟨33733975613903263417333205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22489317075935508944888803 33733975613903263417333205)
                  ·
                    refine ⟨790640053450857736343747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33733975613903263417333205 790640053450857736343747)
                    ·
                      rfl

theorem cell23_4619298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_4619298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619298 prefixEnd_4619298 := by exact prefixLift 4619298
  have htrace : WordTrace (prefixWord ++ tailWord_4619298) baseStart_4619298 baseEnd_4619298 := by
    simpa [prefixWord, tailWord_4619298, baseEnd_4619298] using wordTrace_append hprefix tailTrace_4619298
  have hstable : (prefixWord ++ tailWord_4619298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619298).length < 2 ^ (prefixWord ++ tailWord_4619298).sum := by decide
  have hdescent : baseEnd_4619298 < baseStart_4619298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619335 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_4619335 : Nat := 118140960795 + 4619335 * 2 ^ 59
def prefixEnd_4619335 : Nat := 4983230072969 + 3 ^ 40 * 4619335 * 2
def baseEnd_4619335 : Nat := 2371939159136789564268571

theorem tailTrace_4619335 : CollatzResearch.WordTrace tailWord_4619335 prefixEnd_4619335 2371939159136789564268571 := by
  unfold tailWord_4619335
  simp only [CollatzResearch.WordTrace]
  refine ⟨168480988719945689454011459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112320659146630459636007639 168480988719945689454011459)
  ·
    refine ⟨252721483079918534181017189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168480988719945689454011459 252721483079918534181017189)
    ·
      refine ⟨47385278077484725158940723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252721483079918534181017189 47385278077484725158940723)
      ·
        refine ⟨71077917116227087738411085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47385278077484725158940723 71077917116227087738411085)
        ·
          refine ⟨26654218918585157901904157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71077917116227087738411085 26654218918585157901904157)
          ·
            refine ⟨9995332094469434213214059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26654218918585157901904157 9995332094469434213214059)
            ·
              refine ⟨14992998141704151319821089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9995332094469434213214059 14992998141704151319821089)
              ·
                refine ⟨11244748606278113489865817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14992998141704151319821089 11244748606278113489865817)
                ·
                  refine ⟨8433561454708585117399363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11244748606278113489865817 8433561454708585117399363)
                  ·
                    refine ⟨12650342182062877676099045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8433561454708585117399363 12650342182062877676099045)
                    ·
                      refine ⟨2371939159136789564268571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12650342182062877676099045 2371939159136789564268571)
                      ·
                        rfl

theorem cell23_4619335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_4619335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619335 prefixEnd_4619335 := by exact prefixLift 4619335
  have htrace : WordTrace (prefixWord ++ tailWord_4619335) baseStart_4619335 baseEnd_4619335 := by
    simpa [prefixWord, tailWord_4619335, baseEnd_4619335] using wordTrace_append hprefix tailTrace_4619335
  have hstable : (prefixWord ++ tailWord_4619335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619335).length < 2 ^ (prefixWord ++ tailWord_4619335).sum := by decide
  have hdescent : baseEnd_4619335 < baseStart_4619335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619345 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 3, 4]
def baseStart_4619345 : Nat := 118140960795 + 4619345 * 2 ^ 59
def prefixEnd_4619345 : Nat := 4983230072969 + 3 ^ 40 * 4619345 * 2
def baseEnd_4619345 : Nat := 790648097981111508381175

theorem tailTrace_4619345 : CollatzResearch.WordTrace tailWord_4619345 prefixEnd_4619345 790648097981111508381175 := by
  unfold tailWord_4619345
  simp only [CollatzResearch.WordTrace]
  refine ⟨168481353449909461161875489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112320902299939640774583659 168481353449909461161875489)
  ·
    refine ⟨126361015087432095871406617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168481353449909461161875489 126361015087432095871406617)
    ·
      refine ⟨94770761315574071903554963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126361015087432095871406617 94770761315574071903554963)
      ·
        refine ⟨142156141973361107855332445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94770761315574071903554963 142156141973361107855332445)
        ·
          refine ⟨53308553240010415445749667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142156141973361107855332445 53308553240010415445749667)
          ·
            refine ⟨79962829860015623168624501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53308553240010415445749667 79962829860015623168624501)
            ·
              refine ⟨7496515299376464672058547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79962829860015623168624501 7496515299376464672058547)
              ·
                refine ⟨11244772949064697008087821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7496515299376464672058547 11244772949064697008087821)
                ·
                  refine ⟨4216789855899261378032933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11244772949064697008087821 4216789855899261378032933)
                  ·
                    refine ⟨790648097981111508381175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4216789855899261378032933 790648097981111508381175)
                    ·
                      rfl

theorem cell23_4619345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_4619345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619345 prefixEnd_4619345 := by exact prefixLift 4619345
  have htrace : WordTrace (prefixWord ++ tailWord_4619345) baseStart_4619345 baseEnd_4619345 := by
    simpa [prefixWord, tailWord_4619345, baseEnd_4619345] using wordTrace_append hprefix tailTrace_4619345
  have hstable : (prefixWord ++ tailWord_4619345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619345).length < 2 ^ (prefixWord ++ tailWord_4619345).sum := by decide
  have hdescent : baseEnd_4619345 < baseStart_4619345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619348 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_4619348 : Nat := 118140960795 + 4619348 * 2 ^ 59
def prefixEnd_4619348 : Nat := 4983230072969 + 3 ^ 40 * 4619348 * 2
def baseEnd_4619348 : Nat := 2371945834385298013406011

theorem tailTrace_4619348 : CollatzResearch.WordTrace tailWord_4619348 prefixEnd_4619348 2371945834385298013406011 := by
  unfold tailWord_4619348
  simp only [CollatzResearch.WordTrace]
  refine ⟨84240731434449296337117349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112320975245932395116156465 84240731434449296337117349)
  ·
    refine ⟨15795137143959243063209503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84240731434449296337117349 15795137143959243063209503)
    ·
      refine ⟨23692705715938864594814255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15795137143959243063209503 23692705715938864594814255)
      ·
        refine ⟨35539058573908296892221383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23692705715938864594814255 35539058573908296892221383)
        ·
          refine ⟨53308587860862445338332075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35539058573908296892221383 53308587860862445338332075)
          ·
            refine ⟨79962881791293668007498113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53308587860862445338332075 79962881791293668007498113)
            ·
              refine ⟨59972161343470251005623585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79962881791293668007498113 59972161343470251005623585)
              ·
                refine ⟨44979121007602688254217689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59972161343470251005623585 44979121007602688254217689)
                ·
                  refine ⟨33734340755702016190663267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44979121007602688254217689 33734340755702016190663267)
                  ·
                    refine ⟨50601511133553024285994901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33734340755702016190663267 50601511133553024285994901)
                    ·
                      refine ⟨2371945834385298013406011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50601511133553024285994901 2371945834385298013406011)
                      ·
                        rfl

theorem cell23_4619348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_4619348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619348 prefixEnd_4619348 := by exact prefixLift 4619348
  have htrace : WordTrace (prefixWord ++ tailWord_4619348) baseStart_4619348 baseEnd_4619348 := by
    simpa [prefixWord, tailWord_4619348, baseEnd_4619348] using wordTrace_append hprefix tailTrace_4619348
  have hstable : (prefixWord ++ tailWord_4619348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619348).length < 2 ^ (prefixWord ++ tailWord_4619348).sum := by decide
  have hdescent : baseEnd_4619348 < baseStart_4619348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619396 : List Nat := [2, 3, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_4619396 : Nat := 118140960795 + 4619396 * 2 ^ 59
def prefixEnd_4619396 : Nat := 4983230072969 + 3 ^ 40 * 4619396 * 2
def baseEnd_4619396 : Nat := 790656827152237941868597

theorem tailTrace_4619396 : CollatzResearch.WordTrace tailWord_4619396 prefixEnd_4619396 790656827152237941868597 := by
  unfold tailWord_4619396
  simp only [CollatzResearch.WordTrace]
  refine ⟨84241606786362348435991021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112322142381816464581321361 84241606786362348435991021)
  ·
    refine ⟨31590602544885880663496633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84241606786362348435991021 31590602544885880663496633)
    ·
      refine ⟨23692951908664410497622475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31590602544885880663496633 23692951908664410497622475)
      ·
        refine ⟨35539427862996615746433713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23692951908664410497622475 35539427862996615746433713)
        ·
          refine ⟨26654570897247461809825285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35539427862996615746433713 26654570897247461809825285)
          ·
            refine ⟨4997732043233899089342241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26654570897247461809825285 4997732043233899089342241)
            ·
              refine ⟨3748299032425424317006681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4997732043233899089342241 3748299032425424317006681)
              ·
                refine ⟨2811224274319068237755011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3748299032425424317006681 2811224274319068237755011)
                ·
                  refine ⟨4216836411478602356632517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811224274319068237755011 4216836411478602356632517)
                  ·
                    refine ⟨790656827152237941868597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4216836411478602356632517 790656827152237941868597)
                    ·
                      rfl

theorem cell23_4619396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_4619396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619396 prefixEnd_4619396 := by exact prefixLift 4619396
  have htrace : WordTrace (prefixWord ++ tailWord_4619396) baseStart_4619396 baseEnd_4619396 := by
    simpa [prefixWord, tailWord_4619396, baseEnd_4619396] using wordTrace_append hprefix tailTrace_4619396
  have hstable : (prefixWord ++ tailWord_4619396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619396).length < 2 ^ (prefixWord ++ tailWord_4619396).sum := by decide
  have hdescent : baseEnd_4619396 < baseStart_4619396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619402 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_4619402 : Nat := 118140960795 + 4619402 * 2 ^ 59
def prefixEnd_4619402 : Nat := 4983230072969 + 3 ^ 40 * 4619402 * 2
def baseEnd_4619402 : Nat := 2371973562340640802130763

theorem tailTrace_4619402 : CollatzResearch.WordTrace tailWord_4619402 prefixEnd_4619402 2371973562340640802130763 := by
  unfold tailWord_4619402
  simp only [CollatzResearch.WordTrace]
  refine ⟨42120858102675739974175115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112322288273801973264466973 42120858102675739974175115)
  ·
    refine ⟨63181287154013609961262673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42120858102675739974175115 63181287154013609961262673)
    ·
      refine ⟨47385965365510207470947005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63181287154013609961262673 47385965365510207470947005)
      ·
        refine ⟨17769737012066327801605127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47385965365510207470947005 17769737012066327801605127)
        ·
          refine ⟨26654605518099491702407691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17769737012066327801605127 26654605518099491702407691)
          ·
            refine ⟨39981908277149237553611537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26654605518099491702407691 39981908277149237553611537)
            ·
              refine ⟨29986431207861928165208653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39981908277149237553611537 29986431207861928165208653)
              ·
                refine ⟨11244911702948223061953245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29986431207861928165208653 11244911702948223061953245)
                ·
                  refine ⟨4216841888605583648232467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11244911702948223061953245 4216841888605583648232467)
                  ·
                    refine ⟨6325262832908375472348701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4216841888605583648232467 6325262832908375472348701)
                    ·
                      refine ⟨2371973562340640802130763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6325262832908375472348701 2371973562340640802130763)
                      ·
                        rfl

theorem cell23_4619402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_4619402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619402 prefixEnd_4619402 := by exact prefixLift 4619402
  have htrace : WordTrace (prefixWord ++ tailWord_4619402) baseStart_4619402 baseEnd_4619402 := by
    simpa [prefixWord, tailWord_4619402, baseEnd_4619402] using wordTrace_append hprefix tailTrace_4619402
  have hstable : (prefixWord ++ tailWord_4619402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619402).length < 2 ^ (prefixWord ++ tailWord_4619402).sum := by decide
  have hdescent : baseEnd_4619402 < baseStart_4619402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619422 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_4619422 : Nat := 118140960795 + 4619422 * 2 ^ 59
def prefixEnd_4619422 : Nat := 4983230072969 + 3 ^ 40 * 4619422 * 2
def baseEnd_4619422 : Nat := 790661277317910241293557

theorem tailTrace_4619422 : CollatzResearch.WordTrace tailWord_4619422 prefixEnd_4619422 790661277317910241293557 := by
  unfold tailWord_4619422
  simp only [CollatzResearch.WordTrace]
  refine ⟨21060520233828812914053565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112322774580420335541619013 21060520233828812914053565)
  ·
    refine ⟨7897695087685804842770087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21060520233828812914053565 7897695087685804842770087)
    ·
      refine ⟨11846542631528707264155131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7897695087685804842770087 11846542631528707264155131)
      ·
        refine ⟨17769813947293060896232697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11846542631528707264155131 17769813947293060896232697)
        ·
          refine ⟨13327360460469795672174523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17769813947293060896232697 13327360460469795672174523)
          ·
            refine ⟨19991040690704693508261785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13327360460469795672174523 19991040690704693508261785)
            ·
              refine ⟨14993280518028520131196339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19991040690704693508261785 14993280518028520131196339)
              ·
                refine ⟨22489920777042780196794509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14993280518028520131196339 22489920777042780196794509)
                ·
                  refine ⟨8433720291391042573797941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22489920777042780196794509 8433720291391042573797941)
                  ·
                    refine ⟨790661277317910241293557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8433720291391042573797941 790661277317910241293557)
                    ·
                      rfl

theorem cell23_4619422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_4619422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4619422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4619422 prefixEnd_4619422 := by exact prefixLift 4619422
  have htrace : WordTrace (prefixWord ++ tailWord_4619422) baseStart_4619422 baseEnd_4619422 := by
    simpa [prefixWord, tailWord_4619422, baseEnd_4619422] using wordTrace_append hprefix tailTrace_4619422
  have hstable : (prefixWord ++ tailWord_4619422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619422).length < 2 ^ (prefixWord ++ tailWord_4619422).sum := by decide
  have hdescent : baseEnd_4619422 < baseStart_4619422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
