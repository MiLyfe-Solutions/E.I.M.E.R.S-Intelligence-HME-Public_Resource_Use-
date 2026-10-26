import V185TrunkScan21Chunk125

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1535077 : List Nat := [1, 3, 1, 3, 2, 1, 5, 5]
def baseStart_1535077 : Nat := 118140960795 + 1535077 * 2 ^ 59
def prefixEnd_1535077 : Nat := 4983230072969 + 3 ^ 40 * 1535077 * 2
def baseEnd_1535077 : Nat := 116775161875851220426343

theorem tailTrace_1535077 : CollatzResearch.WordTrace tailWord_1535077 prefixEnd_1535077 116775161875851220426343 := by
  unfold tailWord_1535077
  simp only [CollatzResearch.WordTrace]
  refine ⟨55988857859685674124267485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37325905239790449416178323 55988857859685674124267485)
  ·
    refine ⟨20995821697382127796600307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55988857859685674124267485 20995821697382127796600307)
    ·
      refine ⟨31493732546073191694900461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20995821697382127796600307 31493732546073191694900461)
      ·
        refine ⟨11810149704777446885587673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31493732546073191694900461 11810149704777446885587673)
        ·
          refine ⟨8857612278583085164190755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11810149704777446885587673 8857612278583085164190755)
          ·
            refine ⟨13286418417874627746286133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8857612278583085164190755 13286418417874627746286133)
            ·
              refine ⟨1245601726675746351214325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13286418417874627746286133 1245601726675746351214325)
              ·
                refine ⟨116775161875851220426343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1245601726675746351214325 116775161875851220426343)
                ·
                  rfl

theorem cell21_1535077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 5].length) (baseStart_1535077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535077 prefixEnd_1535077 := by exact prefixLift 1535077
  have htrace : WordTrace (prefixWord ++ tailWord_1535077) baseStart_1535077 baseEnd_1535077 := by
    simpa [prefixWord, tailWord_1535077, baseEnd_1535077] using wordTrace_append hprefix tailTrace_1535077
  have hstable : (prefixWord ++ tailWord_1535077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535077).length < 2 ^ (prefixWord ++ tailWord_1535077).sum := by decide
  have hdescent : baseEnd_1535077 < baseStart_1535077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535108 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_1535108 : Nat := 118140960795 + 1535108 * 2 ^ 59
def prefixEnd_1535108 : Nat := 4983230072969 + 3 ^ 40 * 1535108 * 2
def baseEnd_1535108 : Nat := 350332560249904496262299

theorem tailTrace_1535108 : CollatzResearch.WordTrace tailWord_1535108 prefixEnd_1535108 350332560249904496262299 := by
  unfold tailWord_1535108
  simp only [CollatzResearch.WordTrace]
  refine ⟨27994994261286683209322989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37326659015048910945763985 27994994261286683209322989)
  ·
    refine ⟨10498122847982506203496121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27994994261286683209322989 10498122847982506203496121)
    ·
      refine ⟨7873592135986879652622091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10498122847982506203496121 7873592135986879652622091)
      ·
        refine ⟨11810388203980319478933137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7873592135986879652622091 11810388203980319478933137)
        ·
          refine ⟨8857791152985239609199853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11810388203980319478933137 8857791152985239609199853)
          ·
            refine ⟨3321671682369464853449945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8857791152985239609199853 3321671682369464853449945)
            ·
              refine ⟨2491253761777098640087459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3321671682369464853449945 2491253761777098640087459)
              ·
                refine ⟨3736880642665647960131189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491253761777098640087459 3736880642665647960131189)
                ·
                  refine ⟨350332560249904496262299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3736880642665647960131189 350332560249904496262299)
                  ·
                    rfl

theorem cell21_1535108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_1535108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535108 prefixEnd_1535108 := by exact prefixLift 1535108
  have htrace : WordTrace (prefixWord ++ tailWord_1535108) baseStart_1535108 baseEnd_1535108 := by
    simpa [prefixWord, tailWord_1535108, baseEnd_1535108] using wordTrace_append hprefix tailTrace_1535108
  have hstable : (prefixWord ++ tailWord_1535108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535108).length < 2 ^ (prefixWord ++ tailWord_1535108).sum := by decide
  have hdescent : baseEnd_1535108 < baseStart_1535108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535136 : List Nat := [2, 1, 1, 4, 2, 1, 3, 7]
def baseStart_1535136 : Nat := 118140960795 + 1535136 * 2 ^ 59
def prefixEnd_1535136 : Nat := 4983230072969 + 3 ^ 40 * 1535136 * 2
def baseEnd_1535136 : Nat := 116779650077127556598525

theorem tailTrace_1535136 : CollatzResearch.WordTrace tailWord_1535136 prefixEnd_1535136 116779650077127556598525 := by
  unfold tailWord_1535136
  simp only [CollatzResearch.WordTrace]
  refine ⟨27995504883235963600332631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37327339844314618133776841 27995504883235963600332631)
  ·
    refine ⟨41993257324853945400498947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27995504883235963600332631 41993257324853945400498947)
    ·
      refine ⟨62989885987280918100748421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41993257324853945400498947 62989885987280918100748421)
      ·
        refine ⟨11810603622615172143890329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62989885987280918100748421 11810603622615172143890329)
        ·
          refine ⟨8857952716961379107917747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11810603622615172143890329 8857952716961379107917747)
          ·
            refine ⟨13286929075442068661876621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8857952716961379107917747 13286929075442068661876621)
            ·
              refine ⟨4982598403290775748203733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13286929075442068661876621 4982598403290775748203733)
              ·
                refine ⟨116779650077127556598525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4982598403290775748203733 116779650077127556598525)
                ·
                  rfl

theorem cell21_1535136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_1535136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535136 prefixEnd_1535136 := by exact prefixLift 1535136
  have htrace : WordTrace (prefixWord ++ tailWord_1535136) baseStart_1535136 baseEnd_1535136 := by
    simpa [prefixWord, tailWord_1535136, baseEnd_1535136] using wordTrace_append hprefix tailTrace_1535136
  have hstable : (prefixWord ++ tailWord_1535136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535136).length < 2 ^ (prefixWord ++ tailWord_1535136).sum := by decide
  have hdescent : baseEnd_1535136 < baseStart_1535136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535153 : List Nat := [1, 2, 2, 5, 1, 3, 7]
def baseStart_1535153 : Nat := 118140960795 + 1535153 * 2 ^ 59
def prefixEnd_1535153 : Nat := 4983230072969 + 3 ^ 40 * 1535153 * 2
def baseEnd_1535153 : Nat := 38926981095888268668023

theorem tailTrace_1535153 : CollatzResearch.WordTrace tailWord_1535153 prefixEnd_1535153 38926981095888268668023 := by
  unfold tailWord_1535153
  simp only [CollatzResearch.WordTrace]
  refine ⟨55991629807410339104034113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37327753204940226069356075 55991629807410339104034113)
  ·
    refine ⟨41993722355557754328025585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55991629807410339104034113 41993722355557754328025585)
    ·
      refine ⟨31495291766668315746019189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41993722355557754328025585 31495291766668315746019189)
      ·
        refine ⟨2952683603125154601189299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31495291766668315746019189 2952683603125154601189299)
        ·
          refine ⟨4429025404687731901783949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952683603125154601189299 4429025404687731901783949)
          ·
            refine ⟨1660884526757899463168981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4429025404687731901783949 1660884526757899463168981)
            ·
              refine ⟨38926981095888268668023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1660884526757899463168981 38926981095888268668023)
              ·
                rfl

theorem cell21_1535153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 7].length) (baseStart_1535153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535153 prefixEnd_1535153 := by exact prefixLift 1535153
  have htrace : WordTrace (prefixWord ++ tailWord_1535153) baseStart_1535153 baseEnd_1535153 := by
    simpa [prefixWord, tailWord_1535153, baseEnd_1535153] using wordTrace_append hprefix tailTrace_1535153
  have hstable : (prefixWord ++ tailWord_1535153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535153).length < 2 ^ (prefixWord ++ tailWord_1535153).sum := by decide
  have hdescent : baseEnd_1535153 < baseStart_1535153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535167 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 5]
def baseStart_1535167 : Nat := 118140960795 + 1535167 * 2 ^ 59
def prefixEnd_1535167 : Nat := 4983230072969 + 3 ^ 40 * 1535167 * 2
def baseEnd_1535167 : Nat := 350346024853733504778845

theorem tailTrace_1535167 : CollatzResearch.WordTrace tailWord_1535167 prefixEnd_1535167 350346024853733504778845 := by
  unfold tailWord_1535167
  simp only [CollatzResearch.WordTrace]
  refine ⟨55992140429359619495043755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37328093619573079663362503 55992140429359619495043755)
  ·
    refine ⟨83988210644039429242565633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55992140429359619495043755 83988210644039429242565633)
    ·
      refine ⟨62991157983029571931924225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83988210644039429242565633 62991157983029571931924225)
      ·
        refine ⟨47243368487272178948943169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62991157983029571931924225 47243368487272178948943169)
        ·
          refine ⟨35432526365454134211707377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47243368487272178948943169 35432526365454134211707377)
          ·
            refine ⟨26574394774090600658780533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35432526365454134211707377 26574394774090600658780533)
            ·
              refine ⟨2491349510070993811760675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26574394774090600658780533 2491349510070993811760675)
              ·
                refine ⟨3737024265106490717641013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491349510070993811760675 3737024265106490717641013)
                ·
                  refine ⟨350346024853733504778845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3737024265106490717641013 350346024853733504778845)
                  ·
                    rfl

theorem cell21_1535167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 5].length) (baseStart_1535167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535167 prefixEnd_1535167 := by exact prefixLift 1535167
  have htrace : WordTrace (prefixWord ++ tailWord_1535167) baseStart_1535167 baseEnd_1535167 := by
    simpa [prefixWord, tailWord_1535167, baseEnd_1535167] using wordTrace_append hprefix tailTrace_1535167
  have hstable : (prefixWord ++ tailWord_1535167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535167).length < 2 ^ (prefixWord ++ tailWord_1535167).sum := by decide
  have hdescent : baseEnd_1535167 < baseStart_1535167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535215 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 4]
def baseStart_1535215 : Nat := 118140960795 + 1535215 * 2 ^ 59
def prefixEnd_1535215 : Nat := 4983230072969 + 3 ^ 40 * 1535215 * 2
def baseEnd_1535215 : Nat := 350356979107696087978747

theorem tailTrace_1535215 : CollatzResearch.WordTrace tailWord_1535215 prefixEnd_1535215 350356979107696087978747 := by
  unfold tailWord_1535215
  simp only [CollatzResearch.WordTrace]
  refine ⟨55993891133185723692791099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37329260755457149128527399 55993891133185723692791099)
  ·
    refine ⟨83990836699778585539186649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55993891133185723692791099 83990836699778585539186649)
    ·
      refine ⟨62993127524833939154389987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83990836699778585539186649 62993127524833939154389987)
      ·
        refine ⟨94489691287250908731584981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62993127524833939154389987 94489691287250908731584981)
        ·
          refine ⟨2214602139544943173396523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 94489691287250908731584981 2214602139544943173396523)
          ·
            refine ⟨3321903209317414760094785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214602139544943173396523 3321903209317414760094785)
            ·
              refine ⟨2491427406988061070071089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3321903209317414760094785 2491427406988061070071089)
              ·
                refine ⟨1868570555241045802553317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2491427406988061070071089 1868570555241045802553317)
                ·
                  refine ⟨350356979107696087978747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868570555241045802553317 350356979107696087978747)
                  ·
                    rfl

theorem cell21_1535215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 4].length) (baseStart_1535215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535215 prefixEnd_1535215 := by exact prefixLift 1535215
  have htrace : WordTrace (prefixWord ++ tailWord_1535215) baseStart_1535215 baseEnd_1535215 := by
    simpa [prefixWord, tailWord_1535215, baseEnd_1535215] using wordTrace_append hprefix tailTrace_1535215
  have hstable : (prefixWord ++ tailWord_1535215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535215).length < 2 ^ (prefixWord ++ tailWord_1535215).sum := by decide
  have hdescent : baseEnd_1535215 < baseStart_1535215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535243 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 5]
def baseStart_1535243 : Nat := 118140960795 + 1535243 * 2 ^ 59
def prefixEnd_1535243 : Nat := 4983230072969 + 3 ^ 40 * 1535243 * 2
def baseEnd_1535243 : Nat := 350363369089174261512023

theorem tailTrace_1535243 : CollatzResearch.WordTrace tailWord_1535243 prefixEnd_1535243 350363369089174261512023 := by
  unfold tailWord_1535243
  simp only [CollatzResearch.WordTrace]
  refine ⟨55994912377084284474810383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37329941584722856316540255 55994912377084284474810383)
  ·
    refine ⟨83992368565626426712215575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55994912377084284474810383 83992368565626426712215575)
    ·
      refine ⟨125988552848439640068323363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83992368565626426712215575 125988552848439640068323363)
      ·
        refine ⟨188982829272659460102485045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125988552848439640068323363 188982829272659460102485045)
        ·
          refine ⟨17717140244311824384607973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188982829272659460102485045 17717140244311824384607973)
          ·
            refine ⟨3321963795808467072113995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17717140244311824384607973 3321963795808467072113995)
            ·
              refine ⟨4982945693712700608170993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321963795808467072113995 4982945693712700608170993)
              ·
                refine ⟨3737209270284525456128245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4982945693712700608170993 3737209270284525456128245)
                ·
                  refine ⟨350363369089174261512023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3737209270284525456128245 350363369089174261512023)
                  ·
                    rfl

theorem cell21_1535243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 5].length) (baseStart_1535243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535243 prefixEnd_1535243 := by exact prefixLift 1535243
  have htrace : WordTrace (prefixWord ++ tailWord_1535243) baseStart_1535243 baseEnd_1535243 := by
    simpa [prefixWord, tailWord_1535243, baseEnd_1535243] using wordTrace_append hprefix tailTrace_1535243
  have hstable : (prefixWord ++ tailWord_1535243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535243).length < 2 ^ (prefixWord ++ tailWord_1535243).sum := by decide
  have hdescent : baseEnd_1535243 < baseStart_1535243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535260 : List Nat := [2, 2, 3, 1, 1, 1, 3, 5, 3]
def baseStart_1535260 : Nat := 118140960795 + 1535260 * 2 ^ 59
def prefixEnd_1535260 : Nat := 4983230072969 + 3 ^ 40 * 1535260 * 2
def baseEnd_1535260 : Nat := 350367248720786009728655

theorem tailTrace_1535260 : CollatzResearch.WordTrace tailWord_1535260 prefixEnd_1535260 350367248720786009728655 := by
  unfold tailWord_1535260
  simp only [CollatzResearch.WordTrace]
  refine ⟨27997766209011348189089617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37330354945348464252119489 27997766209011348189089617)
  ·
    refine ⟨20998324656758511141817213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27997766209011348189089617 20998324656758511141817213)
    ·
      refine ⟨7874371746284441678181455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20998324656758511141817213 7874371746284441678181455)
      ·
        refine ⟨11811557619426662517272183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7874371746284441678181455 11811557619426662517272183)
        ·
          refine ⟨17717336429139993775908275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11811557619426662517272183 17717336429139993775908275)
          ·
            refine ⟨26576004643709990663862413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17717336429139993775908275 26576004643709990663862413)
            ·
              refine ⟨9966001741391246498948405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26576004643709990663862413 9966001741391246498948405)
              ·
                refine ⟨934312663255429359276413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9966001741391246498948405 934312663255429359276413)
                ·
                  refine ⟨350367248720786009728655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 934312663255429359276413 350367248720786009728655)
                  ·
                    rfl

theorem cell21_1535260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_1535260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535260 prefixEnd_1535260 := by exact prefixLift 1535260
  have htrace : WordTrace (prefixWord ++ tailWord_1535260) baseStart_1535260 baseEnd_1535260 := by
    simpa [prefixWord, tailWord_1535260, baseEnd_1535260] using wordTrace_append hprefix tailTrace_1535260
  have hstable : (prefixWord ++ tailWord_1535260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535260).length < 2 ^ (prefixWord ++ tailWord_1535260).sum := by decide
  have hdescent : baseEnd_1535260 < baseStart_1535260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535277 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1535277 : Nat := 118140960795 + 1535277 * 2 ^ 59
def prefixEnd_1535277 : Nat := 4983230072969 + 3 ^ 40 * 1535277 * 2
def baseEnd_1535277 : Nat := 350371128352397757945287

theorem tailTrace_1535277 : CollatzResearch.WordTrace tailWord_1535277 prefixEnd_1535277 350371128352397757945287 := by
  unfold tailWord_1535277
  simp only [CollatzResearch.WordTrace]
  refine ⟨55996152458961108281548085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37330768305974072187698723 55996152458961108281548085)
  ·
    refine ⟨5249639293027603901395133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55996152458961108281548085 5249639293027603901395133)
    ·
      refine ⟨1968614734885351463023175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5249639293027603901395133 1968614734885351463023175)
      ·
        refine ⟨2952922102328027194534763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968614734885351463023175 2952922102328027194534763)
        ·
          refine ⟨4429383153492040791802145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952922102328027194534763 4429383153492040791802145)
          ·
            refine ⟨3322037365119030593851609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4429383153492040791802145 3322037365119030593851609)
            ·
              refine ⟨2491528023839272945388707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3322037365119030593851609 2491528023839272945388707)
              ·
                refine ⟨3737292035758909418083061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491528023839272945388707 3737292035758909418083061)
                ·
                  refine ⟨350371128352397757945287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3737292035758909418083061 350371128352397757945287)
                  ·
                    rfl

theorem cell21_1535277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1535277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535277 prefixEnd_1535277 := by exact prefixLift 1535277
  have htrace : WordTrace (prefixWord ++ tailWord_1535277) baseStart_1535277 baseEnd_1535277 := by
    simpa [prefixWord, tailWord_1535277, baseEnd_1535277] using wordTrace_append hprefix tailTrace_1535277
  have hstable : (prefixWord ++ tailWord_1535277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535277).length < 2 ^ (prefixWord ++ tailWord_1535277).sum := by decide
  have hdescent : baseEnd_1535277 < baseStart_1535277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535333 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 6]
def baseStart_1535333 : Nat := 118140960795 + 1535333 * 2 ^ 59
def prefixEnd_1535333 : Nat := 4983230072969 + 3 ^ 40 * 1535333 * 2
def baseEnd_1535333 : Nat := 350383908315354105011839

theorem tailTrace_1535333 : CollatzResearch.WordTrace tailWord_1535333 prefixEnd_1535333 350383908315354105011839 := by
  unfold tailWord_1535333
  simp only [CollatzResearch.WordTrace]
  refine ⟨55998194946758229845586653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37332129964505486563724435 55998194946758229845586653)
  ·
    refine ⟨20999323105034336192094995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55998194946758229845586653 20999323105034336192094995)
    ·
      refine ⟨31498984657551504288142493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20999323105034336192094995 31498984657551504288142493)
      ·
        refine ⟨11812119246581814108053435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31498984657551504288142493 11812119246581814108053435)
        ·
          refine ⟨17718178869872721162080153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11812119246581814108053435 17718178869872721162080153)
          ·
            refine ⟨13288634152404540871560115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17718178869872721162080153 13288634152404540871560115)
            ·
              refine ⟨19932951228606811307340173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13288634152404540871560115 19932951228606811307340173)
              ·
                refine ⟨7474856710727554240252565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19932951228606811307340173 7474856710727554240252565)
                ·
                  refine ⟨350383908315354105011839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7474856710727554240252565 350383908315354105011839)
                  ·
                    rfl

theorem cell21_1535333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_1535333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535333 prefixEnd_1535333 := by exact prefixLift 1535333
  have htrace : WordTrace (prefixWord ++ tailWord_1535333) baseStart_1535333 baseEnd_1535333 := by
    simpa [prefixWord, tailWord_1535333, baseEnd_1535333] using wordTrace_append hprefix tailTrace_1535333
  have hstable : (prefixWord ++ tailWord_1535333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535333).length < 2 ^ (prefixWord ++ tailWord_1535333).sum := by decide
  have hdescent : baseEnd_1535333 < baseStart_1535333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535342 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_1535342 : Nat := 118140960795 + 1535342 * 2 ^ 59
def prefixEnd_1535342 : Nat := 4983230072969 + 3 ^ 40 * 1535342 * 2
def baseEnd_1535342 : Nat := 350385962237972089361821

theorem tailTrace_1535342 : CollatzResearch.WordTrace tailWord_1535342 prefixEnd_1535342 350385962237972089361821 := by
  unfold tailWord_1535342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6999815400465703047833035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37332348802483749588442853 6999815400465703047833035)
  ·
    refine ⟨10499723100698554571749553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6999815400465703047833035 10499723100698554571749553)
    ·
      refine ⟨7874792325523915928812165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10499723100698554571749553 7874792325523915928812165)
      ·
        refine ⟨1476523561035734236652281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7874792325523915928812165 1476523561035734236652281)
        ·
          refine ⟨1107392670776800677489211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1476523561035734236652281 1107392670776800677489211)
          ·
            refine ⟨1661089006165201016233817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107392670776800677489211 1661089006165201016233817)
            ·
              refine ⟨1245816754623900762175363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1661089006165201016233817 1245816754623900762175363)
              ·
                refine ⟨1868725131935851143263045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245816754623900762175363 1868725131935851143263045)
                ·
                  refine ⟨350385962237972089361821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868725131935851143263045 350385962237972089361821)
                  ·
                    rfl

theorem cell21_1535342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_1535342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535342 prefixEnd_1535342 := by exact prefixLift 1535342
  have htrace : WordTrace (prefixWord ++ tailWord_1535342) baseStart_1535342 baseEnd_1535342 := by
    simpa [prefixWord, tailWord_1535342, baseEnd_1535342] using wordTrace_append hprefix tailTrace_1535342
  have hstable : (prefixWord ++ tailWord_1535342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535342).length < 2 ^ (prefixWord ++ tailWord_1535342).sum := by decide
  have hdescent : baseEnd_1535342 < baseStart_1535342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535364 : List Nat := [2, 3, 2, 1, 1, 3, 2, 7]
def baseStart_1535364 : Nat := 118140960795 + 1535364 * 2 ^ 59
def prefixEnd_1535364 : Nat := 4983230072969 + 3 ^ 40 * 1535364 * 2
def baseEnd_1535364 : Nat := 116796994312568313331703

theorem tailTrace_1535364 : CollatzResearch.WordTrace tailWord_1535364 prefixEnd_1535364 116796994312568313331703 := by
  unfold tailWord_1535364
  simp only [CollatzResearch.WordTrace]
  refine ⟨27999662804822961069982573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37332883739763948093310097 27999662804822961069982573)
  ·
    refine ⟨10499873551808610401243465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27999662804822961069982573 10499873551808610401243465)
    ·
      refine ⟨7874905163856457800932599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10499873551808610401243465 7874905163856457800932599)
      ·
        refine ⟨11812357745784686701398899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7874905163856457800932599 11812357745784686701398899)
        ·
          refine ⟨17718536618677030052098349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11812357745784686701398899 17718536618677030052098349)
          ·
            refine ⟨6644451232003886269536881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17718536618677030052098349 6644451232003886269536881)
            ·
              refine ⟨4983338424002914702152661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6644451232003886269536881 4983338424002914702152661)
              ·
                refine ⟨116796994312568313331703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4983338424002914702152661 116796994312568313331703)
                ·
                  rfl

theorem cell21_1535364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_1535364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535364 prefixEnd_1535364 := by exact prefixLift 1535364
  have htrace : WordTrace (prefixWord ++ tailWord_1535364) baseStart_1535364 baseEnd_1535364 := by
    simpa [prefixWord, tailWord_1535364, baseEnd_1535364] using wordTrace_append hprefix tailTrace_1535364
  have hstable : (prefixWord ++ tailWord_1535364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535364).length < 2 ^ (prefixWord ++ tailWord_1535364).sum := by decide
  have hdescent : baseEnd_1535364 < baseStart_1535364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535423 : List Nat := [1, 1, 2, 2, 2, 1, 1, 11]
def baseStart_1535423 : Nat := 118140960795 + 1535423 * 2 ^ 59
def prefixEnd_1535423 : Nat := 4983230072969 + 3 ^ 40 * 1535423 * 2
def baseEnd_1535423 : Nat := 116801482513844649503885

theorem tailTrace_1535423 : CollatzResearch.WordTrace tailWord_1535423 prefixEnd_1535423 116801482513844649503885 := by
  unfold tailWord_1535423
  simp only [CollatzResearch.WordTrace]
  refine ⟨56001477516432175216362923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37334318344288116810908615 56001477516432175216362923)
  ·
    refine ⟨84002216274648262824544385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56001477516432175216362923 84002216274648262824544385)
    ·
      refine ⟨63001662205986197118408289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84002216274648262824544385 63001662205986197118408289)
      ·
        refine ⟨47251246654489647838806217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63001662205986197118408289 47251246654489647838806217)
        ·
          refine ⟨35438434990867235879104663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47251246654489647838806217 35438434990867235879104663)
          ·
            refine ⟨53157652486300853818656995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35438434990867235879104663 53157652486300853818656995)
            ·
              refine ⟨79736478729451280727985493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53157652486300853818656995 79736478729451280727985493)
              ·
                refine ⟨116801482513844649503885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 79736478729451280727985493 116801482513844649503885)
                ·
                  rfl

theorem cell21_1535423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 11].length) (baseStart_1535423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535423 prefixEnd_1535423 := by exact prefixLift 1535423
  have htrace : WordTrace (prefixWord ++ tailWord_1535423) baseStart_1535423 baseEnd_1535423 := by
    simpa [prefixWord, tailWord_1535423, baseEnd_1535423] using wordTrace_append hprefix tailTrace_1535423
  have hstable : (prefixWord ++ tailWord_1535423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535423).length < 2 ^ (prefixWord ++ tailWord_1535423).sum := by decide
  have hdescent : baseEnd_1535423 < baseStart_1535423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535474 : List Nat := [3, 2, 1, 4, 1, 3, 2, 5]
def baseStart_1535474 : Nat := 118140960795 + 1535474 * 2 ^ 59
def prefixEnd_1535474 : Nat := 4983230072969 + 3 ^ 40 * 1535474 * 2
def baseEnd_1535474 : Nat := 116805362145456397720517

theorem tailTrace_1535474 : CollatzResearch.WordTrace tailWord_1535474 prefixEnd_1535474 116805362145456397720517 := by
  unfold tailWord_1535474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14000834409811852731617369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37335558426164940617646317 14000834409811852731617369)
  ·
    refine ⟨10500625807358889548713027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14000834409811852731617369 10500625807358889548713027)
    ·
      refine ⟨15750938711038334323069541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10500625807358889548713027 15750938711038334323069541)
      ·
        refine ⟨2953301008319687685575539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15750938711038334323069541 2953301008319687685575539)
        ·
          refine ⟨4429951512479531528363309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2953301008319687685575539 4429951512479531528363309)
          ·
            refine ⟨1661231817179824323136241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4429951512479531528363309 1661231817179824323136241)
            ·
              refine ⟨1245923862884868242352181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1661231817179824323136241 1245923862884868242352181)
              ·
                refine ⟨116805362145456397720517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1245923862884868242352181 116805362145456397720517)
                ·
                  rfl

theorem cell21_1535474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_1535474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535474 prefixEnd_1535474 := by exact prefixLift 1535474
  have htrace : WordTrace (prefixWord ++ tailWord_1535474) baseStart_1535474 baseEnd_1535474 := by
    simpa [prefixWord, tailWord_1535474, baseEnd_1535474] using wordTrace_append hprefix tailTrace_1535474
  have hstable : (prefixWord ++ tailWord_1535474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535474).length < 2 ^ (prefixWord ++ tailWord_1535474).sum := by decide
  have hdescent : baseEnd_1535474 < baseStart_1535474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535485 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 6]
def baseStart_1535485 : Nat := 118140960795 + 1535485 * 2 ^ 59
def prefixEnd_1535485 : Nat := 4983230072969 + 3 ^ 40 * 1535485 * 2
def baseEnd_1535485 : Nat := 350418596786235618478195

theorem tailTrace_1535485 : CollatzResearch.WordTrace tailWord_1535485 prefixEnd_1535485 350418596786235618478195 := by
  unfold tailWord_1535485
  simp only [CollatzResearch.WordTrace]
  refine ⟨56003738842207559805119909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37335825894805039870079939 56003738842207559805119909)
  ·
    refine ⟨10500701032913917463459983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56003738842207559805119909 10500701032913917463459983)
    ·
      refine ⟨15751051549370876195189975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10500701032913917463459983 15751051549370876195189975)
      ·
        refine ⟨23626577324056314292784963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15751051549370876195189975 23626577324056314292784963)
        ·
          refine ⟨35439865986084471439177445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23626577324056314292784963 35439865986084471439177445)
          ·
            refine ⟨6644974872390838394845771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35439865986084471439177445 6644974872390838394845771)
            ·
              refine ⟨9967462308586257592268657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6644974872390838394845771 9967462308586257592268657)
              ·
                refine ⟨7475596731439693194201493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9967462308586257592268657 7475596731439693194201493)
                ·
                  refine ⟨350418596786235618478195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7475596731439693194201493 350418596786235618478195)
                  ·
                    rfl

theorem cell21_1535485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_1535485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535485 prefixEnd_1535485 := by exact prefixLift 1535485
  have htrace : WordTrace (prefixWord ++ tailWord_1535485) baseStart_1535485 baseEnd_1535485 := by
    simpa [prefixWord, tailWord_1535485, baseEnd_1535485] using wordTrace_append hprefix tailTrace_1535485
  have hstable : (prefixWord ++ tailWord_1535485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535485).length < 2 ^ (prefixWord ++ tailWord_1535485).sum := by decide
  have hdescent : baseEnd_1535485 < baseStart_1535485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535516 : List Nat := [2, 2, 3, 1, 2, 1, 4, 6]
def baseStart_1535516 : Nat := 118140960795 + 1535516 * 2 ^ 59
def prefixEnd_1535516 : Nat := 4983230072969 + 3 ^ 40 * 1535516 * 2
def baseEnd_1535516 : Nat := 116808557136195484487155

theorem tailTrace_1535516 : CollatzResearch.WordTrace tailWord_1535516 prefixEnd_1535516 116808557136195484487155 := by
  unfold tailWord_1535516
  simp only [CollatzResearch.WordTrace]
  refine ⟨28002434752547626049749201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37336579670063501399665601 28002434752547626049749201)
  ·
    refine ⟨21001826064410719537311901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28002434752547626049749201 21001826064410719537311901)
    ·
      refine ⟨7875684774154019826491963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21001826064410719537311901 7875684774154019826491963)
      ·
        refine ⟨11813527161231029739737945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7875684774154019826491963 11813527161231029739737945)
        ·
          refine ⟨8860145370923272304803459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11813527161231029739737945 8860145370923272304803459)
          ·
            refine ⟨13290218056384908457205189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8860145370923272304803459 13290218056384908457205189)
            ·
              refine ⟨2491915885572170335725973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13290218056384908457205189 2491915885572170335725973)
              ·
                refine ⟨116808557136195484487155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2491915885572170335725973 116808557136195484487155)
                ·
                  rfl

theorem cell21_1535516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_1535516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535516 prefixEnd_1535516 := by exact prefixLift 1535516
  have htrace : WordTrace (prefixWord ++ tailWord_1535516) baseStart_1535516 baseEnd_1535516 := by
    simpa [prefixWord, tailWord_1535516, baseEnd_1535516] using wordTrace_append hprefix tailTrace_1535516
  have hstable : (prefixWord ++ tailWord_1535516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535516).length < 2 ^ (prefixWord ++ tailWord_1535516).sum := by decide
  have hdescent : baseEnd_1535516 < baseStart_1535516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535564 : List Nat := [2, 2, 1, 3, 1, 4, 1, 4, 3]
def baseStart_1535564 : Nat := 118140960795 + 1535564 * 2 ^ 59
def prefixEnd_1535564 : Nat := 4983230072969 + 3 ^ 40 * 1535564 * 2
def baseEnd_1535564 : Nat := 350436625662549036661367

theorem tailTrace_1535564 : CollatzResearch.WordTrace tailWord_1535564 prefixEnd_1535564 350436625662549036661367 := by
  unfold tailWord_1535564
  simp only [CollatzResearch.WordTrace]
  refine ⟨28003310104460678148622873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37337746805947570864830497 28003310104460678148622873)
  ·
    refine ⟨21002482578345508611467155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28003310104460678148622873 21002482578345508611467155)
    ·
      refine ⟨31503723867518262917200733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21002482578345508611467155 31503723867518262917200733)
      ·
        refine ⟨11813896450319348593950275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31503723867518262917200733 11813896450319348593950275)
        ·
          refine ⟨17720844675479022890925413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11813896450319348593950275 17720844675479022890925413)
          ·
            refine ⟨3322658376652316792048515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17720844675479022890925413 3322658376652316792048515)
            ·
              refine ⟨4983987564978475188072773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322658376652316792048515 4983987564978475188072773)
              ·
                refine ⟨934497668433464097763645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4983987564978475188072773 934497668433464097763645)
                ·
                  refine ⟨350436625662549036661367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 934497668433464097763645 350436625662549036661367)
                  ·
                    rfl

theorem cell21_1535564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_1535564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535564 prefixEnd_1535564 := by exact prefixLift 1535564
  have htrace : WordTrace (prefixWord ++ tailWord_1535564) baseStart_1535564 baseEnd_1535564 := by
    simpa [prefixWord, tailWord_1535564, baseEnd_1535564] using wordTrace_append hprefix tailTrace_1535564
  have hstable : (prefixWord ++ tailWord_1535564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535564).length < 2 ^ (prefixWord ++ tailWord_1535564).sum := by decide
  have hdescent : baseEnd_1535564 < baseStart_1535564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535581 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 5]
def baseStart_1535581 : Nat := 118140960795 + 1535581 * 2 ^ 59
def prefixEnd_1535581 : Nat := 4983230072969 + 3 ^ 40 * 1535581 * 2
def baseEnd_1535581 : Nat := 350440505294160784877999

theorem tailTrace_1535581 : CollatzResearch.WordTrace tailWord_1535581 prefixEnd_1535581 350440505294160784877999 := by
  unfold tailWord_1535581
  simp only [CollatzResearch.WordTrace]
  refine ⟨56007240249859768200614597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37338160166573178800409731 56007240249859768200614597)
  ·
    refine ⟨10501357546848706537615237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56007240249859768200614597 10501357546848706537615237)
    ·
      refine ⟨1969004540034132475802857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10501357546848706537615237 1969004540034132475802857)
      ·
        refine ⟨1476753405025599356852143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1969004540034132475802857 1476753405025599356852143)
        ·
          refine ⟨2215130107538399035278215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476753405025599356852143 2215130107538399035278215)
          ·
            refine ⟨3322695161307598552917323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215130107538399035278215 3322695161307598552917323)
            ·
              refine ⟨4984042741961397829375985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322695161307598552917323 4984042741961397829375985)
              ·
                refine ⟨3738032056471048372031989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4984042741961397829375985 3738032056471048372031989)
                ·
                  refine ⟨350440505294160784877999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3738032056471048372031989 350440505294160784877999)
                  ·
                    rfl

theorem cell21_1535581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_1535581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535581 prefixEnd_1535581 := by exact prefixLift 1535581
  have htrace : WordTrace (prefixWord ++ tailWord_1535581) baseStart_1535581 baseEnd_1535581 := by
    simpa [prefixWord, tailWord_1535581, baseEnd_1535581] using wordTrace_append hprefix tailTrace_1535581
  have hstable : (prefixWord ++ tailWord_1535581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535581).length < 2 ^ (prefixWord ++ tailWord_1535581).sum := by decide
  have hdescent : baseEnd_1535581 < baseStart_1535581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535623 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 5]
def baseStart_1535623 : Nat := 118140960795 + 1535623 * 2 ^ 59
def prefixEnd_1535623 : Nat := 4983230072969 + 3 ^ 40 * 1535623 * 2
def baseEnd_1535623 : Nat := 350450090266378045177913

theorem tailTrace_1535623 : CollatzResearch.WordTrace tailWord_1535623 prefixEnd_1535623 350450090266378045177913 := by
  unfold tailWord_1535623
  simp only [CollatzResearch.WordTrace]
  refine ⟨56008772115707609373643523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37339181410471739582429015 56008772115707609373643523)
  ·
    refine ⟨84013158173561414060465285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56008772115707609373643523 84013158173561414060465285)
    ·
      refine ⟨15752467157542765136337241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84013158173561414060465285 15752467157542765136337241)
      ·
        refine ⟨11814350368157073852252931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15752467157542765136337241 11814350368157073852252931)
        ·
          refine ⟨17721525552235610778379397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11814350368157073852252931 17721525552235610778379397)
          ·
            refine ⟨3322786041044177020946137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17721525552235610778379397 3322786041044177020946137)
            ·
              refine ⟨2492089530783132765709603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3322786041044177020946137 2492089530783132765709603)
              ·
                refine ⟨3738134296174699148564405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492089530783132765709603 3738134296174699148564405)
                ·
                  refine ⟨350450090266378045177913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3738134296174699148564405 350450090266378045177913)
                  ·
                    rfl

theorem cell21_1535623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 5].length) (baseStart_1535623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535623 prefixEnd_1535623 := by exact prefixLift 1535623
  have htrace : WordTrace (prefixWord ++ tailWord_1535623) baseStart_1535623 baseEnd_1535623 := by
    simpa [prefixWord, tailWord_1535623, baseEnd_1535623] using wordTrace_append hprefix tailTrace_1535623
  have hstable : (prefixWord ++ tailWord_1535623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535623).length < 2 ^ (prefixWord ++ tailWord_1535623).sum := by decide
  have hdescent : baseEnd_1535623 < baseStart_1535623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535637 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 4]
def baseStart_1535637 : Nat := 118140960795 + 1535637 * 2 ^ 59
def prefixEnd_1535637 : Nat := 4983230072969 + 3 ^ 40 * 1535637 * 2
def baseEnd_1535637 : Nat := 350453285257117131944551

theorem tailTrace_1535637 : CollatzResearch.WordTrace tailWord_1535637 prefixEnd_1535637 350453285257117131944551 := by
  unfold tailWord_1535637
  simp only [CollatzResearch.WordTrace]
  refine ⟨56009282737656889764653165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37339521825104593176435443 56009282737656889764653165)
  ·
    refine ⟨21003481026621333661744937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56009282737656889764653165 21003481026621333661744937)
    ·
      refine ⟨15752610769966000246308703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21003481026621333661744937 15752610769966000246308703)
      ·
        refine ⟨23628916154949000369463055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15752610769966000246308703 23628916154949000369463055)
        ·
          refine ⟨35443374232423500554194583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23628916154949000369463055 35443374232423500554194583)
          ·
            refine ⟨53165061348635250831291875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35443374232423500554194583 53165061348635250831291875)
            ·
              refine ⟨79747592022952876246937813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53165061348635250831291875 79747592022952876246937813)
              ·
                refine ⟨1869084188037958037037605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79747592022952876246937813 1869084188037958037037605)
                ·
                  refine ⟨350453285257117131944551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1869084188037958037037605 350453285257117131944551)
                  ·
                    rfl

theorem cell21_1535637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_1535637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535637 prefixEnd_1535637 := by exact prefixLift 1535637
  have htrace : WordTrace (prefixWord ++ tailWord_1535637) baseStart_1535637 baseEnd_1535637 := by
    simpa [prefixWord, tailWord_1535637, baseEnd_1535637] using wordTrace_append hprefix tailTrace_1535637
  have hstable : (prefixWord ++ tailWord_1535637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535637).length < 2 ^ (prefixWord ++ tailWord_1535637).sum := by decide
  have hdescent : baseEnd_1535637 < baseStart_1535637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535651 : List Nat := [1, 1, 1, 4, 1, 1, 5, 7]
def baseStart_1535651 : Nat := 118140960795 + 1535651 * 2 ^ 59
def prefixEnd_1535651 : Nat := 4983230072969 + 3 ^ 40 * 1535651 * 2
def baseEnd_1535651 : Nat := 116818826749285406237063

theorem tailTrace_1535651 : CollatzResearch.WordTrace tailWord_1535651 prefixEnd_1535651 116818826749285406237063 := by
  unfold tailWord_1535651
  simp only [CollatzResearch.WordTrace]
  refine ⟨56009793359606170155662807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37339862239737446770441871 56009793359606170155662807)
  ·
    refine ⟨84014690039409255233494211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56009793359606170155662807 84014690039409255233494211)
    ·
      refine ⟨126022035059113882850241317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84014690039409255233494211 126022035059113882850241317)
      ·
        refine ⟨23629131573583853034420247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126022035059113882850241317 23629131573583853034420247)
        ·
          refine ⟨35443697360375779551630371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23629131573583853034420247 35443697360375779551630371)
          ·
            refine ⟨53165546040563669327445557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35443697360375779551630371 53165546040563669327445557)
            ·
              refine ⟨4984269941302843999448021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53165546040563669327445557 4984269941302843999448021)
              ·
                refine ⟨116818826749285406237063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4984269941302843999448021 116818826749285406237063)
                ·
                  rfl

theorem cell21_1535651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 7].length) (baseStart_1535651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535651 prefixEnd_1535651 := by exact prefixLift 1535651
  have htrace : WordTrace (prefixWord ++ tailWord_1535651) baseStart_1535651 baseEnd_1535651 := by
    simpa [prefixWord, tailWord_1535651, baseEnd_1535651] using wordTrace_append hprefix tailTrace_1535651
  have hstable : (prefixWord ++ tailWord_1535651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535651).length < 2 ^ (prefixWord ++ tailWord_1535651).sum := by decide
  have hdescent : baseEnd_1535651 < baseStart_1535651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535696 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_1535696 : Nat := 118140960795 + 1535696 * 2 ^ 59
def prefixEnd_1535696 : Nat := 4983230072969 + 3 ^ 40 * 1535696 * 2
def baseEnd_1535696 : Nat := 350466749860946140461097

theorem tailTrace_1535696 : CollatzResearch.WordTrace tailWord_1535696 prefixEnd_1535696 350466749860946140461097 := by
  unfold tailWord_1535696
  simp only [CollatzResearch.WordTrace]
  refine ⟨28005717322221571420525471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37340956429628761894033961 28005717322221571420525471)
  ·
    refine ⟨42008575983332357130788207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28005717322221571420525471 42008575983332357130788207)
    ·
      refine ⟨63012863974998535696182311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42008575983332357130788207 63012863974998535696182311)
      ·
        refine ⟨94519295962497803544273467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63012863974998535696182311 94519295962497803544273467)
        ·
          refine ⟨141778943943746705316410201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94519295962497803544273467 141778943943746705316410201)
          ·
            refine ⟨106334207957810028987307651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141778943943746705316410201 106334207957810028987307651)
            ·
              refine ⟨159501311936715043480961477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106334207957810028987307651 159501311936715043480961477)
              ·
                refine ⟨29906495988134070652680277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159501311936715043480961477 29906495988134070652680277)
                ·
                  refine ⟨350466749860946140461097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29906495988134070652680277 350466749860946140461097)
                  ·
                    rfl

theorem cell21_1535696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_1535696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535696 prefixEnd_1535696 := by exact prefixLift 1535696
  have htrace : WordTrace (prefixWord ++ tailWord_1535696) baseStart_1535696 baseEnd_1535696 := by
    simpa [prefixWord, tailWord_1535696, baseEnd_1535696] using wordTrace_append hprefix tailTrace_1535696
  have hstable : (prefixWord ++ tailWord_1535696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535696).length < 2 ^ (prefixWord ++ tailWord_1535696).sum := by decide
  have hdescent : baseEnd_1535696 < baseStart_1535696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535730 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1535730 : Nat := 118140960795 + 1535730 * 2 ^ 59
def prefixEnd_1535730 : Nat := 4983230072969 + 3 ^ 40 * 1535730 * 2
def baseEnd_1535730 : Nat := 350474509124169636894361

theorem tailTrace_1535730 : CollatzResearch.WordTrace tailWord_1535730 prefixEnd_1535730 350474509124169636894361 := by
  unfold tailWord_1535730
  simp only [CollatzResearch.WordTrace]
  refine ⟨14003168681579991661947161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37341783150879977765192429 14003168681579991661947161)
  ·
    refine ⟨10502376511184993746460371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14003168681579991661947161 10502376511184993746460371)
    ·
      refine ⟨15753564766777490619690557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10502376511184993746460371 15753564766777490619690557)
      ·
        refine ⟨5907586787541558982383959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15753564766777490619690557 5907586787541558982383959)
        ·
          refine ⟨8861380181312338473575939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5907586787541558982383959 8861380181312338473575939)
          ·
            refine ⟨13292070271968507710363909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8861380181312338473575939 13292070271968507710363909)
            ·
              refine ⟨2492263175994095195693233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13292070271968507710363909 2492263175994095195693233)
              ·
                refine ⟨1869197381995571396769925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2492263175994095195693233 1869197381995571396769925)
                ·
                  refine ⟨350474509124169636894361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1869197381995571396769925 350474509124169636894361)
                  ·
                    rfl

theorem cell21_1535730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1535730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535730 prefixEnd_1535730 := by exact prefixLift 1535730
  have htrace : WordTrace (prefixWord ++ tailWord_1535730) baseStart_1535730 baseEnd_1535730 := by
    simpa [prefixWord, tailWord_1535730, baseEnd_1535730] using wordTrace_append hprefix tailTrace_1535730
  have hstable : (prefixWord ++ tailWord_1535730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535730).length < 2 ^ (prefixWord ++ tailWord_1535730).sum := by decide
  have hdescent : baseEnd_1535730 < baseStart_1535730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535758 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1535758 : Nat := 118140960795 + 1535758 * 2 ^ 59
def prefixEnd_1535758 : Nat := 4983230072969 + 3 ^ 40 * 1535758 * 2
def baseEnd_1535758 : Nat := 350480899105647810427637

theorem tailTrace_1535758 : CollatzResearch.WordTrace tailWord_1535758 prefixEnd_1535758 350480899105647810427637 := by
  unfold tailWord_1535758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001711996277315928725991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37342463980145684953205285 7001711996277315928725991)
  ·
    refine ⟨10502567994415973893088987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7001711996277315928725991 10502567994415973893088987)
    ·
      refine ⟨15753851991623960839633481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10502567994415973893088987 15753851991623960839633481)
      ·
        refine ⟨11815388993717970629725111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15753851991623960839633481 11815388993717970629725111)
        ·
          refine ⟨17723083490576955944587667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11815388993717970629725111 17723083490576955944587667)
          ·
            refine ⟨26584625235865433916881501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17723083490576955944587667 26584625235865433916881501)
            ·
              refine ⟨9969234463449537718830563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26584625235865433916881501 9969234463449537718830563)
              ·
                refine ⟨14953851695174306578245845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9969234463449537718830563 14953851695174306578245845)
                ·
                  refine ⟨350480899105647810427637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14953851695174306578245845 350480899105647810427637)
                  ·
                    rfl

theorem cell21_1535758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1535758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535758 prefixEnd_1535758 := by exact prefixLift 1535758
  have htrace : WordTrace (prefixWord ++ tailWord_1535758) baseStart_1535758 baseEnd_1535758 := by
    simpa [prefixWord, tailWord_1535758, baseEnd_1535758] using wordTrace_append hprefix tailTrace_1535758
  have hstable : (prefixWord ++ tailWord_1535758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535758).length < 2 ^ (prefixWord ++ tailWord_1535758).sum := by decide
  have hdescent : baseEnd_1535758 < baseStart_1535758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535820 : List Nat := [2, 2, 1, 3, 4, 1, 1, 7]
def baseStart_1535820 : Nat := 118140960795 + 1535820 * 2 ^ 59
def prefixEnd_1535820 : Nat := 4983230072969 + 3 ^ 40 * 1535820 * 2
def baseEnd_1535820 : Nat := 116831682783449826798059

theorem tailTrace_1535820 : CollatzResearch.WordTrace tailWord_1535820 prefixEnd_1535820 116831682783449826798059 := by
  unfold tailWord_1535820
  simp only [CollatzResearch.WordTrace]
  refine ⟨28007978647996956009282457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37343971530662608012376609 28007978647996956009282457)
  ·
    refine ⟨21005983985997717006961843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28007978647996956009282457 21005983985997717006961843)
    ·
      refine ⟨31508975978996575510442765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21005983985997717006961843 31508975978996575510442765)
      ·
        refine ⟨11815865992123715816416037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31508975978996575510442765 11815865992123715816416037)
        ·
          refine ⟨2215474873523196715578007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11815865992123715816416037 2215474873523196715578007)
          ·
            refine ⟨3323212310284795073367011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215474873523196715578007 3323212310284795073367011)
            ·
              refine ⟨4984818465427192610050517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323212310284795073367011 4984818465427192610050517)
              ·
                refine ⟨116831682783449826798059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4984818465427192610050517 116831682783449826798059)
                ·
                  rfl

theorem cell21_1535820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_1535820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535820 prefixEnd_1535820 := by exact prefixLift 1535820
  have htrace : WordTrace (prefixWord ++ tailWord_1535820) baseStart_1535820 baseEnd_1535820 := by
    simpa [prefixWord, tailWord_1535820, baseEnd_1535820] using wordTrace_append hprefix tailTrace_1535820
  have hstable : (prefixWord ++ tailWord_1535820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535820).length < 2 ^ (prefixWord ++ tailWord_1535820).sum := by decide
  have hdescent : baseEnd_1535820 < baseStart_1535820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535865 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 4]
def baseStart_1535865 : Nat := 118140960795 + 1535865 * 2 ^ 59
def prefixEnd_1535865 : Nat := 4983230072969 + 3 ^ 40 * 1535865 * 2
def baseEnd_1535865 : Nat := 350505317963439402144085

theorem tailTrace_1535865 : CollatzResearch.WordTrace tailWord_1535865 prefixEnd_1535865 350505317963439402144085 := by
  unfold tailWord_1535865
  simp only [CollatzResearch.WordTrace]
  refine ⟨56017598580830884703953049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37345065720553923135968699 56017598580830884703953049)
  ·
    refine ⟨42013198935623163527964787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56017598580830884703953049 42013198935623163527964787)
    ·
      refine ⟨63019798403434745291947181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42013198935623163527964787 63019798403434745291947181)
      ·
        refine ⟨23632424401288029484480193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63019798403434745291947181 23632424401288029484480193)
        ·
          refine ⟨17724318300966022113360145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23632424401288029484480193 17724318300966022113360145)
          ·
            refine ⟨13293238725724516585020109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17724318300966022113360145 13293238725724516585020109)
            ·
              refine ⟨4984964522146693719382541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13293238725724516585020109 4984964522146693719382541)
              ·
                refine ⟨1869361695805010144768453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4984964522146693719382541 1869361695805010144768453)
                ·
                  refine ⟨350505317963439402144085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1869361695805010144768453 350505317963439402144085)
                  ·
                    rfl

theorem cell21_1535865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_1535865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535865 prefixEnd_1535865 := by exact prefixLift 1535865
  have htrace : WordTrace (prefixWord ++ tailWord_1535865) baseStart_1535865 baseEnd_1535865 := by
    simpa [prefixWord, tailWord_1535865, baseEnd_1535865] using wordTrace_append hprefix tailTrace_1535865
  have hstable : (prefixWord ++ tailWord_1535865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535865).length < 2 ^ (prefixWord ++ tailWord_1535865).sum := by decide
  have hdescent : baseEnd_1535865 < baseStart_1535865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535896 : List Nat := [2, 1, 2, 6, 1, 9]
def baseStart_1535896 : Nat := 118140960795 + 1535896 * 2 ^ 59
def prefixEnd_1535896 : Nat := 4983230072969 + 3 ^ 40 * 1535896 * 2
def baseEnd_1535896 : Nat := 12981940466140379152865

theorem tailTrace_1535896 : CollatzResearch.WordTrace tailWord_1535896 prefixEnd_1535896 12981940466140379152865 := by
  unfold tailWord_1535896
  simp only [CollatzResearch.WordTrace]
  refine ⟨28009364621859288499165771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37345819495812384665554361 28009364621859288499165771)
  ·
    refine ⟨42014046932788932748748657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28009364621859288499165771 42014046932788932748748657)
    ·
      refine ⟨31510535199591699561561493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42014046932788932748748657 31510535199591699561561493)
      ·
        refine ⟨1477056337480860916948195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31510535199591699561561493 1477056337480860916948195)
        ·
          refine ⟨2215584506221291375422293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477056337480860916948195 2215584506221291375422293)
          ·
            refine ⟨12981940466140379152865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2215584506221291375422293 12981940466140379152865)
            ·
              rfl

theorem cell21_1535896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 9].length) (baseStart_1535896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535896 prefixEnd_1535896 := by exact prefixLift 1535896
  have htrace : WordTrace (prefixWord ++ tailWord_1535896) baseStart_1535896 baseEnd_1535896 := by
    simpa [prefixWord, tailWord_1535896, baseEnd_1535896] using wordTrace_append hprefix tailTrace_1535896
  have hstable : (prefixWord ++ tailWord_1535896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535896).length < 2 ^ (prefixWord ++ tailWord_1535896).sum := by decide
  have hdescent : baseEnd_1535896 < baseStart_1535896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535902 : List Nat := [4, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1535902 : Nat := 118140960795 + 1535902 * 2 ^ 59
def prefixEnd_1535902 : Nat := 4983230072969 + 3 ^ 40 * 1535902 * 2
def baseEnd_1535902 : Nat := 350513761867535560027343

theorem tailTrace_1535902 : CollatzResearch.WordTrace tailWord_1535902 prefixEnd_1535902 350513761867535560027343 := by
  unfold tailWord_1535902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7002368510212105002881245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37345965387797893348699973 7002368510212105002881245)
  ·
    refine ⟨2625888191329539376080467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7002368510212105002881245 2625888191329539376080467)
    ·
      refine ⟨3938832286994309064120701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2625888191329539376080467 3938832286994309064120701)
      ·
        refine ⟨1477062107622865899045263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3938832286994309064120701 1477062107622865899045263)
        ·
          refine ⟨2215593161434298848567895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477062107622865899045263 2215593161434298848567895)
          ·
            refine ⟨3323389742151448272851843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215593161434298848567895 3323389742151448272851843)
            ·
              refine ⟨4985084613227172409277765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323389742151448272851843 4985084613227172409277765)
              ·
                refine ⟨934703364980094826739581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4985084613227172409277765 934703364980094826739581)
                ·
                  refine ⟨350513761867535560027343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 934703364980094826739581 350513761867535560027343)
                  ·
                    rfl

theorem cell21_1535902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1535902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535902 prefixEnd_1535902 := by exact prefixLift 1535902
  have htrace : WordTrace (prefixWord ++ tailWord_1535902) baseStart_1535902 baseEnd_1535902 := by
    simpa [prefixWord, tailWord_1535902, baseEnd_1535902] using wordTrace_append hprefix tailTrace_1535902
  have hstable : (prefixWord ++ tailWord_1535902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535902).length < 2 ^ (prefixWord ++ tailWord_1535902).sum := by decide
  have hdescent : baseEnd_1535902 < baseStart_1535902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535944 : List Nat := [2, 1, 3, 1, 4, 2, 2, 3, 3]
def baseStart_1535944 : Nat := 118140960795 + 1535944 * 2 ^ 59
def prefixEnd_1535944 : Nat := 4983230072969 + 3 ^ 40 * 1535944 * 2
def baseEnd_1535944 : Nat := 350523346839752820327257

theorem tailTrace_1535944 : CollatzResearch.WordTrace tailWord_1535944 prefixEnd_1535944 350523346839752820327257 := by
  unfold tailWord_1535944
  simp only [CollatzResearch.WordTrace]
  refine ⟨28010239973772340598039443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37346986631696454130719257 28010239973772340598039443)
  ·
    refine ⟨42015359960658510897059165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28010239973772340598039443 42015359960658510897059165)
    ·
      refine ⟨15755759985246941586397187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42015359960658510897059165 15755759985246941586397187)
      ·
        refine ⟨23633639977870412379595781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15755759985246941586397187 23633639977870412379595781)
        ·
          refine ⟨4431307495850702321174209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23633639977870412379595781 4431307495850702321174209)
          ·
            refine ⟨3323480621888026740880657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4431307495850702321174209 3323480621888026740880657)
            ·
              refine ⟨2492610466416020055660493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3323480621888026740880657 2492610466416020055660493)
              ·
                refine ⟨934728924906007520872685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2492610466416020055660493 934728924906007520872685)
                ·
                  refine ⟨350523346839752820327257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 934728924906007520872685 350523346839752820327257)
                  ·
                    rfl

theorem cell21_1535944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 3].length) (baseStart_1535944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535944 prefixEnd_1535944 := by exact prefixLift 1535944
  have htrace : WordTrace (prefixWord ++ tailWord_1535944) baseStart_1535944 baseEnd_1535944 := by
    simpa [prefixWord, tailWord_1535944, baseEnd_1535944] using wordTrace_append hprefix tailTrace_1535944
  have hstable : (prefixWord ++ tailWord_1535944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535944).length < 2 ^ (prefixWord ++ tailWord_1535944).sum := by decide
  have hdescent : baseEnd_1535944 < baseStart_1535944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535975 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 4]
def baseStart_1535975 : Nat := 118140960795 + 1535975 * 2 ^ 59
def prefixEnd_1535975 : Nat := 4983230072969 + 3 ^ 40 * 1535975 * 2
def baseEnd_1535975 : Nat := 350530421462103655310527

theorem tailTrace_1535975 : CollatzResearch.WordTrace tailWord_1535975 prefixEnd_1535975 350530421462103655310527 := by
  unfold tailWord_1535975
  simp only [CollatzResearch.WordTrace]
  refine ⟨56021610610432373490457379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37347740406954915660304919 56021610610432373490457379)
  ·
    refine ⟨84032415915648560235686069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56021610610432373490457379 84032415915648560235686069)
    ·
      refine ⟨7878038992092052522095569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84032415915648560235686069 7878038992092052522095569)
      ·
        refine ⟨5908529244069039391571677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7878038992092052522095569 5908529244069039391571677)
        ·
          refine ⟨2215698466525889771839379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5908529244069039391571677 2215698466525889771839379)
          ·
            refine ⟨3323547699788834657759069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215698466525889771839379 3323547699788834657759069)
            ·
              refine ⟨1246330387420812996659651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3323547699788834657759069 1246330387420812996659651)
              ·
                refine ⟨1869495581131219494989477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246330387420812996659651 1869495581131219494989477)
                ·
                  refine ⟨350530421462103655310527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1869495581131219494989477 350530421462103655310527)
                  ·
                    rfl

theorem cell21_1535975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 4].length) (baseStart_1535975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1535975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1535975 prefixEnd_1535975 := by exact prefixLift 1535975
  have htrace : WordTrace (prefixWord ++ tailWord_1535975) baseStart_1535975 baseEnd_1535975 := by
    simpa [prefixWord, tailWord_1535975, baseEnd_1535975] using wordTrace_append hprefix tailTrace_1535975
  have hstable : (prefixWord ++ tailWord_1535975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535975).length < 2 ^ (prefixWord ++ tailWord_1535975).sum := by decide
  have hdescent : baseEnd_1535975 < baseStart_1535975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536031 : List Nat := [1, 1, 2, 4, 1, 2, 4, 6]
def baseStart_1536031 : Nat := 118140960795 + 1536031 * 2 ^ 59
def prefixEnd_1536031 : Nat := 4983230072969 + 3 ^ 40 * 1536031 * 2
def baseEnd_1536031 : Nat := 116847733808353334125693

theorem tailTrace_1536031 : CollatzResearch.WordTrace tailWord_1536031 prefixEnd_1536031 116847733808353334125693 := by
  unfold tailWord_1536031
  simp only [CollatzResearch.WordTrace]
  refine ⟨56023653098229495054495947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37349102065486330036330631 56023653098229495054495947)
  ·
    refine ⟨84035479647344242581743921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56023653098229495054495947 84035479647344242581743921)
    ·
      refine ⟨63026609735508181936307941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84035479647344242581743921 63026609735508181936307941)
      ·
        refine ⟨11817489325407784113057739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63026609735508181936307941 11817489325407784113057739)
        ·
          refine ⟨17726233988111676169586609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11817489325407784113057739 17726233988111676169586609)
          ·
            refine ⟨13294675491083757127189957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17726233988111676169586609 13294675491083757127189957)
            ·
              refine ⟨2492751654578204461348117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13294675491083757127189957 2492751654578204461348117)
              ·
                refine ⟨116847733808353334125693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2492751654578204461348117 116847733808353334125693)
                ·
                  rfl

theorem cell21_1536031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 6].length) (baseStart_1536031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536031 prefixEnd_1536031 := by exact prefixLift 1536031
  have htrace : WordTrace (prefixWord ++ tailWord_1536031) baseStart_1536031 baseEnd_1536031 := by
    simpa [prefixWord, tailWord_1536031, baseEnd_1536031] using wordTrace_append hprefix tailTrace_1536031
  have hstable : (prefixWord ++ tailWord_1536031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536031).length < 2 ^ (prefixWord ++ tailWord_1536031).sum := by decide
  have hdescent : baseEnd_1536031 < baseStart_1536031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536076 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_1536076 : Nat := 118140960795 + 1536076 * 2 ^ 59
def prefixEnd_1536076 : Nat := 4983230072969 + 3 ^ 40 * 1536076 * 2
def baseEnd_1536076 : Nat := 350553471038149924126987

theorem tailTrace_1536076 : CollatzResearch.WordTrace tailWord_1536076 prefixEnd_1536076 350553471038149924126987 := by
  unfold tailWord_1536076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28012647191533233869942041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37350196255377645159922721 28012647191533233869942041)
  ·
    refine ⟨21009485393649925402456531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28012647191533233869942041 21009485393649925402456531)
    ·
      refine ⟨31514228090474888103684797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21009485393649925402456531 31514228090474888103684797)
      ·
        refine ⟨11817835533928083038881799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31514228090474888103684797 11817835533928083038881799)
        ·
          refine ⟨17726753300892124558322699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11817835533928083038881799 17726753300892124558322699)
          ·
            refine ⟨26590129951338186837484049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17726753300892124558322699 26590129951338186837484049)
            ·
              refine ⟨19942597463503640128113037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26590129951338186837484049 19942597463503640128113037)
              ·
                refine ⟨7478474048813865048042389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19942597463503640128113037 7478474048813865048042389)
                ·
                  refine ⟨350553471038149924126987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7478474048813865048042389 350553471038149924126987)
                  ·
                    rfl

theorem cell21_1536076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_1536076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536076 prefixEnd_1536076 := by exact prefixLift 1536076
  have htrace : WordTrace (prefixWord ++ tailWord_1536076) baseStart_1536076 baseEnd_1536076 := by
    simpa [prefixWord, tailWord_1536076, baseEnd_1536076] using wordTrace_append hprefix tailTrace_1536076
  have hstable : (prefixWord ++ tailWord_1536076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536076).length < 2 ^ (prefixWord ++ tailWord_1536076).sum := by decide
  have hdescent : baseEnd_1536076 < baseStart_1536076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536138 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_1536138 : Nat := 118140960795 + 1536138 * 2 ^ 59
def prefixEnd_1536138 : Nat := 4983230072969 + 3 ^ 40 * 1536138 * 2
def baseEnd_1536138 : Nat := 350567620282851594093527

theorem tailTrace_1536138 : CollatzResearch.WordTrace tailWord_1536138 prefixEnd_1536138 350567620282851594093527 := by
  unfold tailWord_1536138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14006888927210463082160267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37351703805894568219094045 14006888927210463082160267)
  ·
    refine ⟨21010333390815694623240401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14006888927210463082160267 21010333390815694623240401)
    ·
      refine ⟨15757750043111770967430301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21010333390815694623240401 15757750043111770967430301)
      ·
        refine ⟨5909156266166914112786363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15757750043111770967430301 5909156266166914112786363)
        ·
          refine ⟨8863734399250371169179545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909156266166914112786363 8863734399250371169179545)
          ·
            refine ⟨6647800799437778376884659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8863734399250371169179545 6647800799437778376884659)
            ·
              refine ⟨9971701199156667565326989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6647800799437778376884659 9971701199156667565326989)
              ·
                refine ⟨3739387949683750336997621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9971701199156667565326989 3739387949683750336997621)
                ·
                  refine ⟨350567620282851594093527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3739387949683750336997621 350567620282851594093527)
                  ·
                    rfl

theorem cell21_1536138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_1536138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536138 prefixEnd_1536138 := by exact prefixLift 1536138
  have htrace : WordTrace (prefixWord ++ tailWord_1536138) baseStart_1536138 baseEnd_1536138 := by
    simpa [prefixWord, tailWord_1536138, baseEnd_1536138] using wordTrace_append hprefix tailTrace_1536138
  have hstable : (prefixWord ++ tailWord_1536138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536138).length < 2 ^ (prefixWord ++ tailWord_1536138).sum := by decide
  have hdescent : baseEnd_1536138 < baseStart_1536138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536158 : List Nat := [4, 3, 1, 1, 3, 2, 2, 5]
def baseStart_1536158 : Nat := 118140960795 + 1536158 * 2 ^ 59
def prefixEnd_1536158 : Nat := 4983230072969 + 3 ^ 40 * 1536158 * 2
def baseEnd_1536158 : Nat := 116857394851778667920051

theorem tailTrace_1536158 : CollatzResearch.WordTrace tailWord_1536158 prefixEnd_1536158 116857394851778667920051 := by
  unfold tailWord_1536158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7003535646096174468046141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37352190112512930496246085 7003535646096174468046141)
  ·
    refine ⟨2626325867286065425517303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7003535646096174468046141 2626325867286065425517303)
    ·
      refine ⟨3939488800929098138275955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2626325867286065425517303 3939488800929098138275955)
      ·
        refine ⟨5909233201393647207413933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939488800929098138275955 5909233201393647207413933)
        ·
          refine ⟨2215962450522617702780225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5909233201393647207413933 2215962450522617702780225)
          ·
            refine ⟨1661971837891963277085169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2215962450522617702780225 1661971837891963277085169)
            ·
              refine ⟨1246478878418972457813877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1661971837891963277085169 1246478878418972457813877)
              ·
                refine ⟨116857394851778667920051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1246478878418972457813877 116857394851778667920051)
                ·
                  rfl

theorem cell21_1536158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_1536158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536158 prefixEnd_1536158 := by exact prefixLift 1536158
  have htrace : WordTrace (prefixWord ++ tailWord_1536158) baseStart_1536158 baseEnd_1536158 := by
    simpa [prefixWord, tailWord_1536158, baseEnd_1536158] using wordTrace_append hprefix tailTrace_1536158
  have hstable : (prefixWord ++ tailWord_1536158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536158).length < 2 ^ (prefixWord ++ tailWord_1536158).sum := by decide
  have hdescent : baseEnd_1536158 < baseStart_1536158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536183 : List Nat := [1, 1, 3, 1, 4, 4, 7]
def baseStart_1536183 : Nat := 118140960795 + 1536183 * 2 ^ 59
def prefixEnd_1536183 : Nat := 4983230072969 + 3 ^ 40 * 1536183 * 2
def baseEnd_1536183 : Nat := 38953098877326835093715

theorem tailTrace_1536183 : CollatzResearch.WordTrace tailWord_1536183 prefixEnd_1536183 38953098877326835093715 := by
  unfold tailWord_1536183
  simp only [CollatzResearch.WordTrace]
  refine ⟨56029196993678825014029203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37352797995785883342686135 56029196993678825014029203)
  ·
    refine ⟨84043795490518237521043805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56029196993678825014029203 84043795490518237521043805)
    ·
      refine ⟨31516423308944339070391427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84043795490518237521043805 31516423308944339070391427)
      ·
        refine ⟨47274634963416508605587141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31516423308944339070391427 47274634963416508605587141)
        ·
          refine ⟨8863994055640595363547589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47274634963416508605587141 8863994055640595363547589)
          ·
            refine ⟨1661998885432611630665173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8863994055640595363547589 1661998885432611630665173)
            ·
              refine ⟨38953098877326835093715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1661998885432611630665173 38953098877326835093715)
              ·
                rfl

theorem cell21_1536183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 7].length) (baseStart_1536183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536183 prefixEnd_1536183 := by exact prefixLift 1536183
  have htrace : WordTrace (prefixWord ++ tailWord_1536183) baseStart_1536183 baseEnd_1536183 := by
    simpa [prefixWord, tailWord_1536183, baseEnd_1536183] using wordTrace_append hprefix tailTrace_1536183
  have hstable : (prefixWord ++ tailWord_1536183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536183).length < 2 ^ (prefixWord ++ tailWord_1536183).sum := by decide
  have hdescent : baseEnd_1536183 < baseStart_1536183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536273 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 7]
def baseStart_1536273 : Nat := 118140960795 + 1536273 * 2 ^ 59
def prefixEnd_1536273 : Nat := 4983230072969 + 3 ^ 40 * 1536273 * 2
def baseEnd_1536273 : Nat := 350598429122121359343251

theorem tailTrace_1536273 : CollatzResearch.WordTrace tailWord_1536273 prefixEnd_1536273 350598429122121359343251 := by
  unfold tailWord_1536273
  simp only [CollatzResearch.WordTrace]
  refine ⟨56032479563352770384805473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37354986375568513589870315 56032479563352770384805473)
  ·
    refine ⟨42024359672514577788604105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56032479563352770384805473 42024359672514577788604105)
    ·
      refine ⟨31518269754385933341453079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42024359672514577788604105 31518269754385933341453079)
      ·
        refine ⟨47277404631578900012179619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31518269754385933341453079 47277404631578900012179619)
        ·
          refine ⟨70916106947368350018269429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47277404631578900012179619 70916106947368350018269429)
          ·
            refine ⟨6648385026315782814212759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70916106947368350018269429 6648385026315782814212759)
            ·
              refine ⟨9972577539473674221319139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648385026315782814212759 9972577539473674221319139)
              ·
                refine ⟨14958866309210511331978709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9972577539473674221319139 14958866309210511331978709)
                ·
                  refine ⟨350598429122121359343251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14958866309210511331978709 350598429122121359343251)
                  ·
                    rfl

theorem cell21_1536273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_1536273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536273 prefixEnd_1536273 := by exact prefixLift 1536273
  have htrace : WordTrace (prefixWord ++ tailWord_1536273) baseStart_1536273 baseEnd_1536273 := by
    simpa [prefixWord, tailWord_1536273, baseEnd_1536273] using wordTrace_append hprefix tailTrace_1536273
  have hstable : (prefixWord ++ tailWord_1536273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536273).length < 2 ^ (prefixWord ++ tailWord_1536273).sum := by decide
  have hdescent : baseEnd_1536273 < baseStart_1536273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536304 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_1536304 : Nat := 118140960795 + 1536304 * 2 ^ 59
def prefixEnd_1536304 : Nat := 4983230072969 + 3 ^ 40 * 1536304 * 2
def baseEnd_1536304 : Nat := 350605503744472194326521

theorem tailTrace_1536304 : CollatzResearch.WordTrace tailWord_1536304 prefixEnd_1536304 350605503744472194326521 := by
  unfold tailWord_1536304
  simp only [CollatzResearch.WordTrace]
  refine ⟨28016805113120231339591983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37355740150826975119455977 28016805113120231339591983)
  ·
    refine ⟨42025207669680347009387975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28016805113120231339591983 42025207669680347009387975)
    ·
      refine ⟨63037811504520520514081963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42025207669680347009387975 63037811504520520514081963)
      ·
        refine ⟨94556717256780780771122945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63037811504520520514081963 94556717256780780771122945)
        ·
          refine ⟨70917537942585585578342209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94556717256780780771122945 70917537942585585578342209)
          ·
            refine ⟨53188153456939189183756657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70917537942585585578342209 53188153456939189183756657)
            ·
              refine ⟨39891115092704391887817493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53188153456939189183756657 39891115092704391887817493)
              ·
                refine ⟨1869896019970518369741445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39891115092704391887817493 1869896019970518369741445)
                ·
                  refine ⟨350605503744472194326521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1869896019970518369741445 350605503744472194326521)
                  ·
                    rfl

theorem cell21_1536304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_1536304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536304 prefixEnd_1536304 := by exact prefixLift 1536304
  have htrace : WordTrace (prefixWord ++ tailWord_1536304) baseStart_1536304 baseEnd_1536304 := by
    simpa [prefixWord, tailWord_1536304, baseEnd_1536304] using wordTrace_append hprefix tailTrace_1536304
  have hstable : (prefixWord ++ tailWord_1536304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536304).length < 2 ^ (prefixWord ++ tailWord_1536304).sum := by decide
  have hdescent : baseEnd_1536304 < baseStart_1536304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536341 : List Nat := [1, 3, 2, 2, 5, 1, 1, 3, 3]
def baseStart_1536341 : Nat := 118140960795 + 1536341 * 2 ^ 59
def prefixEnd_1536341 : Nat := 4983230072969 + 3 ^ 40 * 1536341 * 2
def baseEnd_1536341 : Nat := 350613947648568352209779

theorem tailTrace_1536341 : CollatzResearch.WordTrace tailWord_1536341 prefixEnd_1536341 350613947648568352209779 := by
  unfold tailWord_1536341
  simp only [CollatzResearch.WordTrace]
  refine ⟨56034959727106417998280877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37356639818070945332187251 56034959727106417998280877)
  ·
    refine ⟨21013109897664906749355329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56034959727106417998280877 21013109897664906749355329)
    ·
      refine ⟨15759832423248680062016497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21013109897664906749355329 15759832423248680062016497)
      ·
        refine ⟨11819874317436510046512373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15759832423248680062016497 11819874317436510046512373)
        ·
          refine ⟨1108113217259672816860535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11819874317436510046512373 1108113217259672816860535)
          ·
            refine ⟨1662169825889509225290803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108113217259672816860535 1662169825889509225290803)
            ·
              refine ⟨2493254738834263837936205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662169825889509225290803 2493254738834263837936205)
              ·
                refine ⟨934970527062848939226077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2493254738834263837936205 934970527062848939226077)
                ·
                  refine ⟨350613947648568352209779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 934970527062848939226077 350613947648568352209779)
                  ·
                    rfl

theorem cell21_1536341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_1536341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536341 prefixEnd_1536341 := by exact prefixLift 1536341
  have htrace : WordTrace (prefixWord ++ tailWord_1536341) baseStart_1536341 baseEnd_1536341 := by
    simpa [prefixWord, tailWord_1536341, baseEnd_1536341] using wordTrace_append hprefix tailTrace_1536341
  have hstable : (prefixWord ++ tailWord_1536341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536341).length < 2 ^ (prefixWord ++ tailWord_1536341).sum := by decide
  have hdescent : baseEnd_1536341 < baseStart_1536341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536352 : List Nat := [2, 1, 1, 3, 6, 1, 7]
def baseStart_1536352 : Nat := 118140960795 + 1536352 * 2 ^ 59
def prefixEnd_1536352 : Nat := 4983230072969 + 3 ^ 40 * 1536352 * 2
def baseEnd_1536352 : Nat := 38957384222048308614047

theorem tailTrace_1536352 : CollatzResearch.WordTrace tailWord_1536352 prefixEnd_1536352 38957384222048308614047 := by
  unfold tailWord_1536352
  simp only [CollatzResearch.WordTrace]
  refine ⟨28017680465033283438465655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37356907286711044584620873 28017680465033283438465655)
  ·
    refine ⟨42026520697549925157698483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28017680465033283438465655 42026520697549925157698483)
    ·
      refine ⟨63039781046324887736547725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42026520697549925157698483 63039781046324887736547725)
      ·
        refine ⟨23639917892371832901205397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63039781046324887736547725 23639917892371832901205397)
        ·
          refine ⟨1108121151204929667244003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23639917892371832901205397 1108121151204929667244003)
          ·
            refine ⟨1662181726807394500866005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108121151204929667244003 1662181726807394500866005)
            ·
              refine ⟨38957384222048308614047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1662181726807394500866005 38957384222048308614047)
              ·
                rfl

theorem cell21_1536352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 7].length) (baseStart_1536352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536352 prefixEnd_1536352 := by exact prefixLift 1536352
  have htrace : WordTrace (prefixWord ++ tailWord_1536352) baseStart_1536352 baseEnd_1536352 := by
    simpa [prefixWord, tailWord_1536352, baseEnd_1536352] using wordTrace_append hprefix tailTrace_1536352
  have hstable : (prefixWord ++ tailWord_1536352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536352).length < 2 ^ (prefixWord ++ tailWord_1536352).sum := by decide
  have hdescent : baseEnd_1536352 < baseStart_1536352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536414 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1536414 : Nat := 118140960795 + 1536414 * 2 ^ 59
def prefixEnd_1536414 : Nat := 4983230072969 + 3 ^ 40 * 1536414 * 2
def baseEnd_1536414 : Nat := 350630607243136447492963

theorem tailTrace_1536414 : CollatzResearch.WordTrace tailWord_1536414 prefixEnd_1536414 350630607243136447492963 := by
  unfold tailWord_1536414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7004702781980243933211037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37358414837227967643792197 7004702781980243933211037)
  ·
    refine ⟨2626763543242591474954139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7004702781980243933211037 2626763543242591474954139)
    ·
      refine ⟨3940145314863887212431209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2626763543242591474954139 3940145314863887212431209)
      ·
        refine ⟨2955108986147915409323407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3940145314863887212431209 2955108986147915409323407)
        ·
          refine ⟨4432663479221873113985111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2955108986147915409323407 4432663479221873113985111)
          ·
            refine ⟨6648995218832809670977667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4432663479221873113985111 6648995218832809670977667)
            ·
              refine ⟨9973492828249214506466501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648995218832809670977667 9973492828249214506466501)
              ·
                refine ⟨1870029905296727719962469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9973492828249214506466501 1870029905296727719962469)
                ·
                  refine ⟨350630607243136447492963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870029905296727719962469 350630607243136447492963)
                  ·
                    rfl

theorem cell21_1536414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1536414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536414 prefixEnd_1536414 := by exact prefixLift 1536414
  have htrace : WordTrace (prefixWord ++ tailWord_1536414) baseStart_1536414 baseEnd_1536414 := by
    simpa [prefixWord, tailWord_1536414, baseEnd_1536414] using wordTrace_append hprefix tailTrace_1536414
  have hstable : (prefixWord ++ tailWord_1536414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536414).length < 2 ^ (prefixWord ++ tailWord_1536414).sum := by decide
  have hdescent : baseEnd_1536414 < baseStart_1536414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536490 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_1536490 : Nat := 118140960795 + 1536490 * 2 ^ 59
def prefixEnd_1536490 : Nat := 4983230072969 + 3 ^ 40 * 1536490 * 2
def baseEnd_1536490 : Nat := 350647951478577204226141

theorem tailTrace_1536490 : CollatzResearch.WordTrace tailWord_1536490 prefixEnd_1536490 350647951478577204226141 := by
  unfold tailWord_1536490
  simp only [CollatzResearch.WordTrace]
  refine ⟨14010098550891654111363731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37360262802377744296969949 14010098550891654111363731)
  ·
    refine ⟨21015147826337481167045597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14010098550891654111363731 21015147826337481167045597)
    ·
      refine ⟨7880680434876555437642099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21015147826337481167045597 7880680434876555437642099)
      ·
        refine ⟨11821020652314833156463149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7880680434876555437642099 11821020652314833156463149)
        ·
          refine ⟨4432882744618062433673681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11821020652314833156463149 4432882744618062433673681)
          ·
            refine ⟨3324662058463546825255261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4432882744618062433673681 3324662058463546825255261)
            ·
              refine ⟨1246748271923830059470723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3324662058463546825255261 1246748271923830059470723)
              ·
                refine ⟨1870122407885745089206085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246748271923830059470723 1870122407885745089206085)
                ·
                  refine ⟨350647951478577204226141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870122407885745089206085 350647951478577204226141)
                  ·
                    rfl

theorem cell21_1536490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_1536490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536490 prefixEnd_1536490 := by exact prefixLift 1536490
  have htrace : WordTrace (prefixWord ++ tailWord_1536490) baseStart_1536490 baseEnd_1536490 := by
    simpa [prefixWord, tailWord_1536490, baseEnd_1536490] using wordTrace_append hprefix tailTrace_1536490
  have hstable : (prefixWord ++ tailWord_1536490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536490).length < 2 ^ (prefixWord ++ tailWord_1536490).sum := by decide
  have hdescent : baseEnd_1536490 < baseStart_1536490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536515 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 8]
def baseStart_1536515 : Nat := 118140960795 + 1536515 * 2 ^ 59
def prefixEnd_1536515 : Nat := 4983230072969 + 3 ^ 40 * 1536515 * 2
def baseEnd_1536515 : Nat := 350653656819182716309423

theorem tailTrace_1536515 : CollatzResearch.WordTrace tailWord_1536515 prefixEnd_1536515 350653656819182716309423 := by
  unfold tailWord_1536515
  simp only [CollatzResearch.WordTrace]
  refine ⟨56041306028476045715114999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37360870685650697143409999 56041306028476045715114999)
  ·
    refine ⟨84061959042714068572672499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56041306028476045715114999 84061959042714068572672499)
    ·
      refine ⟨126092938564071102859008749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84061959042714068572672499 126092938564071102859008749)
      ·
        refine ⟨47284851961526663572128281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126092938564071102859008749 47284851961526663572128281)
        ·
          refine ⟨35463638971144997679096211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47284851961526663572128281 35463638971144997679096211)
          ·
            refine ⟨53195458456717496518644317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35463638971144997679096211 53195458456717496518644317)
            ·
              refine ⟨19948296921269061194491619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53195458456717496518644317 19948296921269061194491619)
              ·
                refine ⟨29922445381903591791737429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19948296921269061194491619 29922445381903591791737429)
                ·
                  refine ⟨350653656819182716309423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29922445381903591791737429 350653656819182716309423)
                  ·
                    rfl

theorem cell21_1536515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_1536515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536515 prefixEnd_1536515 := by exact prefixLift 1536515
  have htrace : WordTrace (prefixWord ++ tailWord_1536515) baseStart_1536515 baseEnd_1536515 := by
    simpa [prefixWord, tailWord_1536515, baseEnd_1536515] using wordTrace_append hprefix tailTrace_1536515
  have hstable : (prefixWord ++ tailWord_1536515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536515).length < 2 ^ (prefixWord ++ tailWord_1536515).sum := by decide
  have hdescent : baseEnd_1536515 < baseStart_1536515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536549 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 4]
def baseStart_1536549 : Nat := 118140960795 + 1536549 * 2 ^ 59
def prefixEnd_1536549 : Nat := 4983230072969 + 3 ^ 40 * 1536549 * 2
def baseEnd_1536549 : Nat := 350661416082406212742687

theorem tailTrace_1536549 : CollatzResearch.WordTrace tailWord_1536549 prefixEnd_1536549 350661416082406212742687 := by
  unfold tailWord_1536549
  simp only [CollatzResearch.WordTrace]
  refine ⟨56042546110352869521852701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37361697406901913014568467 56042546110352869521852701)
  ·
    refine ⟨21015954791382326070694763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56042546110352869521852701 21015954791382326070694763)
    ·
      refine ⟨31523932187073489106042145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21015954791382326070694763 31523932187073489106042145)
      ·
        refine ⟨23642949140305116829531609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31523932187073489106042145 23642949140305116829531609)
        ·
          refine ⟨17732211855228837622148707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23642949140305116829531609 17732211855228837622148707)
          ·
            refine ⟨26598317782843256433223061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17732211855228837622148707 26598317782843256433223061)
            ·
              refine ⟨1246796146070777645307331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26598317782843256433223061 1246796146070777645307331)
              ·
                refine ⟨1870194219106166467960997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246796146070777645307331 1870194219106166467960997)
                ·
                  refine ⟨350661416082406212742687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870194219106166467960997 350661416082406212742687)
                  ·
                    rfl

theorem cell21_1536549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_1536549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536549 prefixEnd_1536549 := by exact prefixLift 1536549
  have htrace : WordTrace (prefixWord ++ tailWord_1536549) baseStart_1536549 baseEnd_1536549 := by
    simpa [prefixWord, tailWord_1536549, baseEnd_1536549] using wordTrace_append hprefix tailTrace_1536549
  have hstable : (prefixWord ++ tailWord_1536549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536549).length < 2 ^ (prefixWord ++ tailWord_1536549).sum := by decide
  have hdescent : baseEnd_1536549 < baseStart_1536549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536580 : List Nat := [2, 3, 5, 1, 10]
def baseStart_1536580 : Nat := 118140960795 + 1536580 * 2 ^ 59
def prefixEnd_1536580 : Nat := 4983230072969 + 3 ^ 40 * 1536580 * 2
def baseEnd_1536580 : Nat := 4329240625984654910197

theorem tailTrace_1536580 : CollatzResearch.WordTrace tailWord_1536580 prefixEnd_1536580 4329240625984654910197 := by
  unfold tailWord_1536580
  simp only [CollatzResearch.WordTrace]
  refine ⟨28021838386620280908115597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37362451182160374544154129 28021838386620280908115597)
  ·
    refine ⟨10508189394982605340543349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28021838386620280908115597 10508189394982605340543349)
    ·
      refine ⟨985142755779619250675939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10508189394982605340543349 985142755779619250675939)
      ·
        refine ⟨1477714133669428876013909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985142755779619250675939 1477714133669428876013909)
        ·
          refine ⟨4329240625984654910197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1477714133669428876013909 4329240625984654910197)
          ·
            rfl

theorem cell21_1536580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 10].length) (baseStart_1536580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536580 prefixEnd_1536580 := by exact prefixLift 1536580
  have htrace : WordTrace (prefixWord ++ tailWord_1536580) baseStart_1536580 baseEnd_1536580 := by
    simpa [prefixWord, tailWord_1536580, baseEnd_1536580] using wordTrace_append hprefix tailTrace_1536580
  have hstable : (prefixWord ++ tailWord_1536580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536580).length < 2 ^ (prefixWord ++ tailWord_1536580).sum := by decide
  have hdescent : baseEnd_1536580 < baseStart_1536580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536591 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 6]
def baseStart_1536591 : Nat := 118140960795 + 1536591 * 2 ^ 59
def prefixEnd_1536591 : Nat := 4983230072969 + 3 ^ 40 * 1536591 * 2
def baseEnd_1536591 : Nat := 350671001054623473042601

theorem tailTrace_1536591 : CollatzResearch.WordTrace tailWord_1536591 prefixEnd_1536591 350671001054623473042601 := by
  unfold tailWord_1536591
  simp only [CollatzResearch.WordTrace]
  refine ⟨56044077976200710694881627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37362718650800473796587751 56044077976200710694881627)
  ·
    refine ⟨84066116964301066042322441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56044077976200710694881627 84066116964301066042322441)
    ·
      refine ⟨63049587723225799531741831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84066116964301066042322441 63049587723225799531741831)
      ·
        refine ⟨94574381584838699297612747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63049587723225799531741831 94574381584838699297612747)
        ·
          refine ⟨141861572377258048946419121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94574381584838699297612747 141861572377258048946419121)
          ·
            refine ⟨106396179282943536709814341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141861572377258048946419121 106396179282943536709814341)
            ·
              refine ⟨19949283615551913133090189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106396179282943536709814341 19949283615551913133090189)
              ·
                refine ⟨7480981355831967424908821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19949283615551913133090189 7480981355831967424908821)
                ·
                  refine ⟨350671001054623473042601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7480981355831967424908821 350671001054623473042601)
                  ·
                    rfl

theorem cell21_1536591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_1536591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536591 prefixEnd_1536591 := by exact prefixLift 1536591
  have htrace : WordTrace (prefixWord ++ tailWord_1536591) baseStart_1536591 baseEnd_1536591 := by
    simpa [prefixWord, tailWord_1536591, baseEnd_1536591] using wordTrace_append hprefix tailTrace_1536591
  have hstable : (prefixWord ++ tailWord_1536591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536591).length < 2 ^ (prefixWord ++ tailWord_1536591).sum := by decide
  have hdescent : baseEnd_1536591 < baseStart_1536591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536608 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_1536608 : Nat := 118140960795 + 1536608 * 2 ^ 59
def prefixEnd_1536608 : Nat := 4983230072969 + 3 ^ 40 * 1536608 * 2
def baseEnd_1536608 : Nat := 350674880686235221259233

theorem tailTrace_1536608 : CollatzResearch.WordTrace tailWord_1536608 prefixEnd_1536608 350674880686235221259233 := by
  unfold tailWord_1536608
  simp only [CollatzResearch.WordTrace]
  refine ⟨28022349008569561299125239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37363132011426081732166985 28022349008569561299125239)
  ·
    refine ⟨42033523512854341948687859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28022349008569561299125239 42033523512854341948687859)
    ·
      refine ⟨63050285269281512923031789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42033523512854341948687859 63050285269281512923031789)
      ·
        refine ⟨23643856975980567346136921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63050285269281512923031789 23643856975980567346136921)
        ·
          refine ⟨17732892731985425509602691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23643856975980567346136921 17732892731985425509602691)
          ·
            refine ⟨26599339097978138264404037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17732892731985425509602691 26599339097978138264404037)
            ·
              refine ⟨4987376080870900924575757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26599339097978138264404037 4987376080870900924575757)
              ·
                refine ⟨1870266030326587846715909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4987376080870900924575757 1870266030326587846715909)
                ·
                  refine ⟨350674880686235221259233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870266030326587846715909 350674880686235221259233)
                  ·
                    rfl

theorem cell21_1536608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_1536608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536608 prefixEnd_1536608 := by exact prefixLift 1536608
  have htrace : WordTrace (prefixWord ++ tailWord_1536608) baseStart_1536608 baseEnd_1536608 := by
    simpa [prefixWord, tailWord_1536608, baseEnd_1536608] using wordTrace_append hprefix tailTrace_1536608
  have hstable : (prefixWord ++ tailWord_1536608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536608).length < 2 ^ (prefixWord ++ tailWord_1536608).sum := by decide
  have hdescent : baseEnd_1536608 < baseStart_1536608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536670 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1536670 : Nat := 118140960795 + 1536670 * 2 ^ 59
def prefixEnd_1536670 : Nat := 4983230072969 + 3 ^ 40 * 1536670 * 2
def baseEnd_1536670 : Nat := 350689029930936891225773

theorem tailTrace_1536670 : CollatzResearch.WordTrace tailWord_1536670 prefixEnd_1536670 350689029930936891225773 := by
  unfold tailWord_1536670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7005869917864313398375933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37364639561943004791338309 7005869917864313398375933)
  ·
    refine ⟨2627201219199117524390975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7005869917864313398375933 2627201219199117524390975)
    ·
      refine ⟨3940801828798676286586463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2627201219199117524390975 3940801828798676286586463)
      ·
        refine ⟨5911202743198014429879695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3940801828798676286586463 5911202743198014429879695)
        ·
          refine ⟨8866804114797021644819543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911202743198014429879695 8866804114797021644819543)
          ·
            refine ⟨13300206172195532467229315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8866804114797021644819543 13300206172195532467229315)
            ·
              refine ⟨19950309258293298700843973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13300206172195532467229315 19950309258293298700843973)
              ·
                refine ⟨3740682985929993506408245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19950309258293298700843973 3740682985929993506408245)
                ·
                  refine ⟨350689029930936891225773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3740682985929993506408245 350689029930936891225773)
                  ·
                    rfl

theorem cell21_1536670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1536670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536670 prefixEnd_1536670 := by exact prefixLift 1536670
  have htrace : WordTrace (prefixWord ++ tailWord_1536670) baseStart_1536670 baseEnd_1536670 := by
    simpa [prefixWord, tailWord_1536670, baseEnd_1536670] using wordTrace_append hprefix tailTrace_1536670
  have hstable : (prefixWord ++ tailWord_1536670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536670).length < 2 ^ (prefixWord ++ tailWord_1536670).sum := by decide
  have hdescent : baseEnd_1536670 < baseStart_1536670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536673 : List Nat := [1, 2, 3, 3, 4, 1, 2, 5]
def baseStart_1536673 : Nat := 118140960795 + 1536673 * 2 ^ 59
def prefixEnd_1536673 : Nat := 4983230072969 + 3 ^ 40 * 1536673 * 2
def baseEnd_1536673 : Nat := 116896571523936517558589

theorem tailTrace_1536673 : CollatzResearch.WordTrace tailWord_1536673 prefixEnd_1536673 116896571523936517558589 := by
  unfold tailWord_1536673
  simp only [CollatzResearch.WordTrace]
  refine ⟨56047068761903638699366673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37364712507935759132911115 56047068761903638699366673)
  ·
    refine ⟨42035301571427729024525005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56047068761903638699366673 42035301571427729024525005)
    ·
      refine ⟨15763238089285398384196877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42035301571427729024525005 15763238089285398384196877)
      ·
        refine ⟨5911214283482024394073829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15763238089285398384196877 5911214283482024394073829)
        ·
          refine ⟨1108352678152879573888843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5911214283482024394073829 1108352678152879573888843)
          ·
            refine ⟨1662529017229319360833265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108352678152879573888843 1662529017229319360833265)
            ·
              refine ⟨1246896762921989520624949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1662529017229319360833265 1246896762921989520624949)
              ·
                refine ⟨116896571523936517558589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1246896762921989520624949 116896571523936517558589)
                ·
                  rfl

theorem cell21_1536673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 5].length) (baseStart_1536673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536673 prefixEnd_1536673 := by exact prefixLift 1536673
  have htrace : WordTrace (prefixWord ++ tailWord_1536673) baseStart_1536673 baseEnd_1536673 := by
    simpa [prefixWord, tailWord_1536673, baseEnd_1536673] using wordTrace_append hprefix tailTrace_1536673
  have hstable : (prefixWord ++ tailWord_1536673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536673).length < 2 ^ (prefixWord ++ tailWord_1536673).sum := by decide
  have hdescent : baseEnd_1536673 < baseStart_1536673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536687 : List Nat := [1, 1, 2, 1, 2, 7, 1, 3, 3]
def baseStart_1536687 : Nat := 118140960795 + 1536687 * 2 ^ 59
def prefixEnd_1536687 : Nat := 4983230072969 + 3 ^ 40 * 1536687 * 2
def baseEnd_1536687 : Nat := 350692909562548639442405

theorem tailTrace_1536687 : CollatzResearch.WordTrace tailWord_1536687 prefixEnd_1536687 350692909562548639442405 := by
  unfold tailWord_1536687
  simp only [CollatzResearch.WordTrace]
  refine ⟨56047579383852919090376315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37365052922568612726917543 56047579383852919090376315)
  ·
    refine ⟨84071369075779378635564473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56047579383852919090376315 84071369075779378635564473)
    ·
      refine ⟨63053526806834533976673355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84071369075779378635564473 63053526806834533976673355)
      ·
        refine ⟨94580290210251800965010033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63053526806834533976673355 94580290210251800965010033)
        ·
          refine ⟨70935217657688850723757525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94580290210251800965010033 70935217657688850723757525)
          ·
            refine ⟨1662544163852082438838067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70935217657688850723757525 1662544163852082438838067)
            ·
              refine ⟨2493816245778123658257101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662544163852082438838067 2493816245778123658257101)
              ·
                refine ⟨935181092166796371846413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2493816245778123658257101 935181092166796371846413)
                ·
                  refine ⟨350692909562548639442405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935181092166796371846413 350692909562548639442405)
                  ·
                    rfl

theorem cell21_1536687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 3].length) (baseStart_1536687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536687 prefixEnd_1536687 := by exact prefixLift 1536687
  have htrace : WordTrace (prefixWord ++ tailWord_1536687) baseStart_1536687 baseEnd_1536687 := by
    simpa [prefixWord, tailWord_1536687, baseEnd_1536687] using wordTrace_append hprefix tailTrace_1536687
  have hstable : (prefixWord ++ tailWord_1536687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536687).length < 2 ^ (prefixWord ++ tailWord_1536687).sum := by decide
  have hdescent : baseEnd_1536687 < baseStart_1536687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536718 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_1536718 : Nat := 118140960795 + 1536718 * 2 ^ 59
def prefixEnd_1536718 : Nat := 4983230072969 + 3 ^ 40 * 1536718 * 2
def baseEnd_1536718 : Nat := 350699984184899474425675

theorem tailTrace_1536718 : CollatzResearch.WordTrace tailWord_1536718 prefixEnd_1536718 350699984184899474425675 := by
  unfold tailWord_1536718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7006088755842576423094351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37365806697827074256503205 7006088755842576423094351)
  ·
    refine ⟨10509133133763864634641527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7006088755842576423094351 10509133133763864634641527)
    ·
      refine ⟨15763699700645796951962291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10509133133763864634641527 15763699700645796951962291)
      ·
        refine ⟨23645549550968695427943437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15763699700645796951962291 23645549550968695427943437)
        ·
          refine ⟨8867081081613260785478789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23645549550968695427943437 8867081081613260785478789)
          ·
            refine ⟨1662577702802486397277273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8867081081613260785478789 1662577702802486397277273)
            ·
              refine ⟨1246933277101864797957955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1662577702802486397277273 1246933277101864797957955)
              ·
                refine ⟨1870399915652797196936933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246933277101864797957955 1870399915652797196936933)
                ·
                  refine ⟨350699984184899474425675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870399915652797196936933 350699984184899474425675)
                  ·
                    rfl

theorem cell21_1536718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_1536718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536718 prefixEnd_1536718 := by exact prefixLift 1536718
  have htrace : WordTrace (prefixWord ++ tailWord_1536718) baseStart_1536718 baseEnd_1536718 := by
    simpa [prefixWord, tailWord_1536718, baseEnd_1536718] using wordTrace_append hprefix tailTrace_1536718
  have hstable : (prefixWord ++ tailWord_1536718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536718).length < 2 ^ (prefixWord ++ tailWord_1536718).sum := by decide
  have hdescent : baseEnd_1536718 < baseStart_1536718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536746 : List Nat := [3, 1, 3, 1, 1, 1, 1, 7, 3]
def baseStart_1536746 : Nat := 118140960795 + 1536746 * 2 ^ 59
def prefixEnd_1536746 : Nat := 4983230072969 + 3 ^ 40 * 1536746 * 2
def baseEnd_1536746 : Nat := 350706374166377647958951

theorem tailTrace_1536746 : CollatzResearch.WordTrace tailWord_1536746 prefixEnd_1536746 350706374166377647958951 := by
  unfold tailWord_1536746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14012432822659793041693523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37366487527092781444516061 14012432822659793041693523)
  ·
    refine ⟨21018649233989689562540285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14012432822659793041693523 21018649233989689562540285)
    ·
      refine ⟨7881993462746133585952607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21018649233989689562540285 7881993462746133585952607)
      ·
        refine ⟨11822990194119200378928911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7881993462746133585952607 11822990194119200378928911)
        ·
          refine ⟨17734485291178800568393367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11822990194119200378928911 17734485291178800568393367)
          ·
            refine ⟨26601727936768200852590051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17734485291178800568393367 26601727936768200852590051)
            ·
              refine ⟨39902591905152301278885077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26601727936768200852590051 39902591905152301278885077)
              ·
                refine ⟨935216997777007061223869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39902591905152301278885077 935216997777007061223869)
                ·
                  refine ⟨350706374166377647958951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935216997777007061223869 350706374166377647958951)
                  ·
                    rfl

theorem cell21_1536746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_1536746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536746 prefixEnd_1536746 := by exact prefixLift 1536746
  have htrace : WordTrace (prefixWord ++ tailWord_1536746) baseStart_1536746 baseEnd_1536746 := by
    simpa [prefixWord, tailWord_1536746, baseEnd_1536746] using wordTrace_append hprefix tailTrace_1536746
  have hstable : (prefixWord ++ tailWord_1536746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536746).length < 2 ^ (prefixWord ++ tailWord_1536746).sum := by decide
  have hdescent : baseEnd_1536746 < baseStart_1536746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536760 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_1536760 : Nat := 118140960795 + 1536760 * 2 ^ 59
def prefixEnd_1536760 : Nat := 4983230072969 + 3 ^ 40 * 1536760 * 2
def baseEnd_1536760 : Nat := 350709569157116734725589

theorem tailTrace_1536760 : CollatzResearch.WordTrace tailWord_1536760 prefixEnd_1536760 350709569157116734725589 := by
  unfold tailWord_1536760
  simp only [CollatzResearch.WordTrace]
  refine ⟨28025120956294226278891867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37366827941725635038522489 28025120956294226278891867)
  ·
    refine ⟨42037681434441339418337801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28025120956294226278891867 42037681434441339418337801)
    ·
      refine ⟨31528261075831004563753351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42037681434441339418337801 31528261075831004563753351)
      ·
        refine ⟨47292391613746506845630027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31528261075831004563753351 47292391613746506845630027)
        ·
          refine ⟨70938587420619760268445041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47292391613746506845630027 70938587420619760268445041)
          ·
            refine ⟨53203940565464820201333781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70938587420619760268445041 53203940565464820201333781)
            ·
              refine ⟨2493934714006163446937521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53203940565464820201333781 2493934714006163446937521)
              ·
                refine ⟨1870451035504622585203141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2493934714006163446937521 1870451035504622585203141)
                ·
                  refine ⟨350709569157116734725589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870451035504622585203141 350709569157116734725589)
                  ·
                    rfl

theorem cell21_1536760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_1536760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536760 prefixEnd_1536760 := by exact prefixLift 1536760
  have htrace : WordTrace (prefixWord ++ tailWord_1536760) baseStart_1536760 baseEnd_1536760 := by
    simpa [prefixWord, tailWord_1536760, baseEnd_1536760] using wordTrace_append hprefix tailTrace_1536760
  have hstable : (prefixWord ++ tailWord_1536760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536760).length < 2 ^ (prefixWord ++ tailWord_1536760).sum := by decide
  have hdescent : baseEnd_1536760 < baseStart_1536760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536850 : List Nat := [3, 2, 2, 1, 1, 2, 3, 7]
def baseStart_1536850 : Nat := 118140960795 + 1536850 * 2 ^ 59
def prefixEnd_1536850 : Nat := 4983230072969 + 3 ^ 40 * 1536850 * 2
def baseEnd_1536850 : Nat := 116910036127765526075135

theorem tailTrace_1536850 : CollatzResearch.WordTrace tailWord_1536850 prefixEnd_1536850 116910036127765526075135 := by
  unfold tailWord_1536850
  simp only [CollatzResearch.WordTrace]
  refine ⟨14013381120565599482140001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37369016321508265285706669 14013381120565599482140001)
  ·
    refine ⟨10510035840424199611605001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14013381120565599482140001 10510035840424199611605001)
    ·
      refine ⟨7882526880318149708703751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10510035840424199611605001 7882526880318149708703751)
      ·
        refine ⟨11823790320477224563055627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7882526880318149708703751 11823790320477224563055627)
        ·
          refine ⟨17735685480715836844583441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11823790320477224563055627 17735685480715836844583441)
          ·
            refine ⟨13301764110536877633437581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17735685480715836844583441 13301764110536877633437581)
            ·
              refine ⟨4988161541451329112539093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13301764110536877633437581 4988161541451329112539093)
              ·
                refine ⟨116910036127765526075135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4988161541451329112539093 116910036127765526075135)
                ·
                  rfl

theorem cell21_1536850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_1536850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536850 prefixEnd_1536850 := by exact prefixLift 1536850
  have htrace : WordTrace (prefixWord ++ tailWord_1536850) baseStart_1536850 baseEnd_1536850 := by
    simpa [prefixWord, tailWord_1536850, baseEnd_1536850] using wordTrace_append hprefix tailTrace_1536850
  have hstable : (prefixWord ++ tailWord_1536850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536850).length < 2 ^ (prefixWord ++ tailWord_1536850).sum := by decide
  have hdescent : baseEnd_1536850 < baseStart_1536850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536881 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 5]
def baseStart_1536881 : Nat := 118140960795 + 1536881 * 2 ^ 59
def prefixEnd_1536881 : Nat := 4983230072969 + 3 ^ 40 * 1536881 * 2
def baseEnd_1536881 : Nat := 350737183005647413208675

theorem tailTrace_1536881 : CollatzResearch.WordTrace tailWord_1536881 prefixEnd_1536881 350737183005647413208675 := by
  unfold tailWord_1536881
  simp only [CollatzResearch.WordTrace]
  refine ⟨56054655145150090222938497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37369770096766726815292331 56054655145150090222938497)
  ·
    refine ⟨42040991358862567667203873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56054655145150090222938497 42040991358862567667203873)
    ·
      refine ⟨31530743519146925750402905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42040991358862567667203873 31530743519146925750402905)
      ·
        refine ⟨23648057639360194312802179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31530743519146925750402905 23648057639360194312802179)
        ·
          refine ⟨35472086459040291469203269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23648057639360194312802179 35472086459040291469203269)
          ·
            refine ⟨6651016211070054650475613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35472086459040291469203269 6651016211070054650475613)
            ·
              refine ⟨2494131079151270493928355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6651016211070054650475613 2494131079151270493928355)
              ·
                refine ⟨3741196618726905740892533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494131079151270493928355 3741196618726905740892533)
                ·
                  refine ⟨350737183005647413208675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3741196618726905740892533 350737183005647413208675)
                  ·
                    rfl

theorem cell21_1536881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_1536881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536881 prefixEnd_1536881 := by exact prefixLift 1536881
  have htrace : WordTrace (prefixWord ++ tailWord_1536881) baseStart_1536881 baseEnd_1536881 := by
    simpa [prefixWord, tailWord_1536881, baseEnd_1536881] using wordTrace_append hprefix tailTrace_1536881
  have hstable : (prefixWord ++ tailWord_1536881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536881).length < 2 ^ (prefixWord ++ tailWord_1536881).sum := by decide
  have hdescent : baseEnd_1536881 < baseStart_1536881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536926 : List Nat := [4, 3, 1, 13]
def baseStart_1536926 : Nat := 118140960795 + 1536926 * 2 ^ 59
def prefixEnd_1536926 : Nat := 4983230072969 + 3 ^ 40 * 1536926 * 2
def baseEnd_1536926 : Nat := 1443405154809618662381

theorem tailTrace_1536926 : CollatzResearch.WordTrace tailWord_1536926 prefixEnd_1536926 1443405154809618662381 := by
  unfold tailWord_1536926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7007037053748382863540829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37370864286658041938884421 7007037053748382863540829)
  ·
    refine ⟨2627638895155643573827811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7007037053748382863540829 2627638895155643573827811)
    ·
      refine ⟨3941458342733465360741717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2627638895155643573827811 3941458342733465360741717)
      ·
        refine ⟨1443405154809618662381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3941458342733465360741717 1443405154809618662381)
        ·
          rfl

theorem cell21_1536926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 13].length) (baseStart_1536926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536926 prefixEnd_1536926 := by exact prefixLift 1536926
  have htrace : WordTrace (prefixWord ++ tailWord_1536926) baseStart_1536926 baseEnd_1536926 := by
    simpa [prefixWord, tailWord_1536926, baseEnd_1536926] using wordTrace_append hprefix tailTrace_1536926
  have hstable : (prefixWord ++ tailWord_1536926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536926).length < 2 ^ (prefixWord ++ tailWord_1536926).sum := by decide
  have hdescent : baseEnd_1536926 < baseStart_1536926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536929 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 4]
def baseStart_1536929 : Nat := 118140960795 + 1536929 * 2 ^ 59
def prefixEnd_1536929 : Nat := 4983230072969 + 3 ^ 40 * 1536929 * 2
def baseEnd_1536929 : Nat := 350748137259609996408577

theorem tailTrace_1536929 : CollatzResearch.WordTrace tailWord_1536929 prefixEnd_1536929 350748137259609996408577 := by
  unfold tailWord_1536929
  simp only [CollatzResearch.WordTrace]
  refine ⟨56056405848976194420685841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37370937232650796280457227 56056405848976194420685841)
  ·
    refine ⟨42042304386732145815514381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56056405848976194420685841 42042304386732145815514381)
    ·
      refine ⟨15765864145024554680817893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42042304386732145815514381 15765864145024554680817893)
      ·
        refine ⟨2956099527192104002653355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15765864145024554680817893 2956099527192104002653355)
        ·
          refine ⟨4434149290788156003980033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956099527192104002653355 4434149290788156003980033)
          ·
            refine ⟨3325611968091117002985025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4434149290788156003980033 3325611968091117002985025)
            ·
              refine ⟨2494208976068337752238769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3325611968091117002985025 2494208976068337752238769)
              ·
                refine ⟨1870656732051253314179077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2494208976068337752238769 1870656732051253314179077)
                ·
                  refine ⟨350748137259609996408577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870656732051253314179077 350748137259609996408577)
                  ·
                    rfl

theorem cell21_1536929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_1536929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536929 prefixEnd_1536929 := by exact prefixLift 1536929
  have htrace : WordTrace (prefixWord ++ tailWord_1536929) baseStart_1536929 baseEnd_1536929 := by
    simpa [prefixWord, tailWord_1536929, baseEnd_1536929] using wordTrace_append hprefix tailTrace_1536929
  have hstable : (prefixWord ++ tailWord_1536929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536929).length < 2 ^ (prefixWord ++ tailWord_1536929).sum := by decide
  have hdescent : baseEnd_1536929 < baseStart_1536929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536974 : List Nat := [4, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_1536974 : Nat := 118140960795 + 1536974 * 2 ^ 59
def prefixEnd_1536974 : Nat := 4983230072969 + 3 ^ 40 * 1536974 * 2
def baseEnd_1536974 : Nat := 350758406872699918158485

theorem tailTrace_1536974 : CollatzResearch.WordTrace tailWord_1536974 prefixEnd_1536974 350758406872699918158485 := by
  unfold tailWord_1536974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7007255891726645888259247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37372031422542111404049317 7007255891726645888259247)
  ·
    refine ⟨10510883837589968832388871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7007255891726645888259247 10510883837589968832388871)
    ·
      refine ⟨15766325756384953248583307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10510883837589968832388871 15766325756384953248583307)
      ·
        refine ⟨23649488634577429872874961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15766325756384953248583307 23649488634577429872874961)
        ·
          refine ⟨17737116475933072404656221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23649488634577429872874961 17737116475933072404656221)
          ·
            refine ⟨6651418678474902151746083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17737116475933072404656221 6651418678474902151746083)
            ·
              refine ⟨9977128017712353227619125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6651418678474902151746083 9977128017712353227619125)
              ·
                refine ⟨935355751660533115089293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9977128017712353227619125 935355751660533115089293)
                ·
                  refine ⟨350758406872699918158485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935355751660533115089293 350758406872699918158485)
                  ·
                    rfl

theorem cell21_1536974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_1536974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1536974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1536974 prefixEnd_1536974 := by exact prefixLift 1536974
  have htrace : WordTrace (prefixWord ++ tailWord_1536974) baseStart_1536974 baseEnd_1536974 := by
    simpa [prefixWord, tailWord_1536974, baseEnd_1536974] using wordTrace_append hprefix tailTrace_1536974
  have hstable : (prefixWord ++ tailWord_1536974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536974).length < 2 ^ (prefixWord ++ tailWord_1536974).sum := by decide
  have hdescent : baseEnd_1536974 < baseStart_1536974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537042 : List Nat := [3, 2, 5, 1, 1, 1, 3, 2, 3]
def baseStart_1537042 : Nat := 118140960795 + 1537042 * 2 ^ 59
def prefixEnd_1537042 : Nat := 4983230072969 + 3 ^ 40 * 1537042 * 2
def baseEnd_1537042 : Nat := 350773925399146911025013

theorem tailTrace_1537042 : CollatzResearch.WordTrace tailWord_1537042 prefixEnd_1537042 350773925399146911025013 := by
  unfold tailWord_1537042
  simp only [CollatzResearch.WordTrace]
  refine ⟨14015131824391703679887345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37373684865044543146366253 14015131824391703679887345)
  ·
    refine ⟨10511348868293777759915509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14015131824391703679887345 10511348868293777759915509)
    ·
      refine ⟨985438956402541664992079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10511348868293777759915509 985438956402541664992079)
      ·
        refine ⟨1478158434603812497488119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985438956402541664992079 1478158434603812497488119)
        ·
          refine ⟨2217237651905718746232179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478158434603812497488119 2217237651905718746232179)
          ·
            refine ⟨3325856477858578119348269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217237651905718746232179 3325856477858578119348269)
            ·
              refine ⟨1247196179196966794755601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3325856477858578119348269 1247196179196966794755601)
              ·
                refine ⟨935397134397725096066701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247196179196966794755601 935397134397725096066701)
                ·
                  refine ⟨350773925399146911025013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935397134397725096066701 350773925399146911025013)
                  ·
                    rfl

theorem cell21_1537042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_1537042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537042 prefixEnd_1537042 := by exact prefixLift 1537042
  have htrace : WordTrace (prefixWord ++ tailWord_1537042) baseStart_1537042 baseEnd_1537042 := by
    simpa [prefixWord, tailWord_1537042, baseEnd_1537042] using wordTrace_append hprefix tailTrace_1537042
  have hstable : (prefixWord ++ tailWord_1537042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537042).length < 2 ^ (prefixWord ++ tailWord_1537042).sum := by decide
  have hdescent : baseEnd_1537042 < baseStart_1537042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537157 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 4]
def baseStart_1537157 : Nat := 118140960795 + 1537157 * 2 ^ 59
def prefixEnd_1537157 : Nat := 4983230072969 + 3 ^ 40 * 1537157 * 2
def baseEnd_1537157 : Nat := 350800169965932266608111

theorem tailTrace_1537157 : CollatzResearch.WordTrace tailWord_1537157 prefixEnd_1537157 350800169965932266608111 := by
  unfold tailWord_1537157
  simp only [CollatzResearch.WordTrace]
  refine ⟨56064721692150189359985725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37376481128100126239990483 56064721692150189359985725)
  ·
    refine ⟨21024270634556321009994647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56064721692150189359985725 21024270634556321009994647)
    ·
      refine ⟨31536405951834481514991971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21024270634556321009994647 31536405951834481514991971)
      ·
        refine ⟨47304608927751722272487957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31536405951834481514991971 47304608927751722272487957)
        ·
          refine ⟨2217403543488361981522873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47304608927751722272487957 2217403543488361981522873)
          ·
            refine ⟨1663052657616271486142155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2217403543488361981522873 1663052657616271486142155)
            ·
              refine ⟨2494578986424407229213233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663052657616271486142155 2494578986424407229213233)
              ·
                refine ⟨1870934239818305421909925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2494578986424407229213233 1870934239818305421909925)
                ·
                  refine ⟨350800169965932266608111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870934239818305421909925 350800169965932266608111)
                  ·
                    rfl

theorem cell21_1537157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_1537157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537157 prefixEnd_1537157 := by exact prefixLift 1537157
  have htrace : WordTrace (prefixWord ++ tailWord_1537157) baseStart_1537157 baseEnd_1537157 := by
    simpa [prefixWord, tailWord_1537157, baseEnd_1537157] using wordTrace_append hprefix tailTrace_1537157
  have hstable : (prefixWord ++ tailWord_1537157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537157).length < 2 ^ (prefixWord ++ tailWord_1537157).sum := by decide
  have hdescent : baseEnd_1537157 < baseStart_1537157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537202 : List Nat := [3, 2, 1, 1, 1, 4, 3, 3, 3]
def baseStart_1537202 : Nat := 118140960795 + 1537202 * 2 ^ 59
def prefixEnd_1537202 : Nat := 4983230072969 + 3 ^ 40 * 1537202 * 2
def baseEnd_1537202 : Nat := 350810439579022188358019

theorem tailTrace_1537202 : CollatzResearch.WordTrace tailWord_1537202 prefixEnd_1537202 350810439579022188358019 := by
  unfold tailWord_1537202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14016590744246790511343465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37377575317991441363582573 14016590744246790511343465)
  ·
    refine ⟨10512443058185092883507599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14016590744246790511343465 10512443058185092883507599)
    ·
      refine ⟨15768664587277639325261399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10512443058185092883507599 15768664587277639325261399)
      ·
        refine ⟨23652996880916458987892099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15768664587277639325261399 23652996880916458987892099)
        ·
          refine ⟨35479495321374688481838149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23652996880916458987892099 35479495321374688481838149)
          ·
            refine ⟨6652405372757754090344653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35479495321374688481838149 6652405372757754090344653)
            ·
              refine ⟨2494652014784157783879245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6652405372757754090344653 2494652014784157783879245)
              ·
                refine ⟨935494505544059168954717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2494652014784157783879245 935494505544059168954717)
                ·
                  refine ⟨350810439579022188358019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935494505544059168954717 350810439579022188358019)
                  ·
                    rfl

theorem cell21_1537202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_1537202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537202 prefixEnd_1537202 := by exact prefixLift 1537202
  have htrace : WordTrace (prefixWord ++ tailWord_1537202) baseStart_1537202 baseEnd_1537202 := by
    simpa [prefixWord, tailWord_1537202, baseEnd_1537202] using wordTrace_append hprefix tailTrace_1537202
  have hstable : (prefixWord ++ tailWord_1537202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537202).length < 2 ^ (prefixWord ++ tailWord_1537202).sum := by decide
  have hdescent : baseEnd_1537202 < baseStart_1537202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537213 : List Nat := [1, 4, 1, 2, 1, 1, 11]
def baseStart_1537213 : Nat := 118140960795 + 1537213 * 2 ^ 59
def prefixEnd_1537213 : Nat := 4983230072969 + 3 ^ 40 * 1537213 * 2
def baseEnd_1537213 : Nat := 38979216658765401519407

theorem tailTrace_1537213 : CollatzResearch.WordTrace tailWord_1537213 prefixEnd_1537213 38979216658765401519407 := by
  unfold tailWord_1537213
  simp only [CollatzResearch.WordTrace]
  refine ⟨56066764179947310924024293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37377842786631540616016195 56066764179947310924024293)
  ·
    refine ⟨10512518283740120798254555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56066764179947310924024293 10512518283740120798254555)
    ·
      refine ⟨15768777425610181197381833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10512518283740120798254555 15768777425610181197381833)
      ·
        refine ⟨11826583069207635898036375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15768777425610181197381833 11826583069207635898036375)
        ·
          refine ⟨17739874603811453847054563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11826583069207635898036375 17739874603811453847054563)
          ·
            refine ⟨26609811905717180770581845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17739874603811453847054563 26609811905717180770581845)
            ·
              refine ⟨38979216658765401519407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26609811905717180770581845 38979216658765401519407)
              ·
                rfl

theorem cell21_1537213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 11].length) (baseStart_1537213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537213 prefixEnd_1537213 := by exact prefixLift 1537213
  have htrace : WordTrace (prefixWord ++ tailWord_1537213) baseStart_1537213 baseEnd_1537213 := by
    simpa [prefixWord, tailWord_1537213, baseEnd_1537213] using wordTrace_append hprefix tailTrace_1537213
  have hstable : (prefixWord ++ tailWord_1537213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537213).length < 2 ^ (prefixWord ++ tailWord_1537213).sum := by decide
  have hdescent : baseEnd_1537213 < baseStart_1537213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537357 : List Nat := [1, 6, 1, 3, 1, 2, 2, 5]
def baseStart_1537357 : Nat := 118140960795 + 1537357 * 2 ^ 59
def prefixEnd_1537357 : Nat := 4983230072969 + 3 ^ 40 * 1537357 * 2
def baseEnd_1537357 : Nat := 116948604230258787758123

theorem tailTrace_1537357 : CollatzResearch.WordTrace tailWord_1537357 prefixEnd_1537357 116948604230258787758123 := by
  unfold tailWord_1537357
  simp only [CollatzResearch.WordTrace]
  refine ⟨56072016291425623517266325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37381344194283749011510883 56072016291425623517266325)
  ·
    refine ⟨2628375763660576102371859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56072016291425623517266325 2628375763660576102371859)
    ·
      refine ⟨3942563645490864153557789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2628375763660576102371859 3942563645490864153557789)
      ·
        refine ⟨1478461367059074057584171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3942563645490864153557789 1478461367059074057584171)
        ·
          refine ⟨2217692050588611086376257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478461367059074057584171 2217692050588611086376257)
          ·
            refine ⟨1663269037941458314782193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2217692050588611086376257 1663269037941458314782193)
            ·
              refine ⟨1247451778456093736086645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1663269037941458314782193 1247451778456093736086645)
              ·
                refine ⟨116948604230258787758123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1247451778456093736086645 116948604230258787758123)
                ·
                  rfl

theorem cell21_1537357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 5].length) (baseStart_1537357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537357 prefixEnd_1537357 := by exact prefixLift 1537357
  have htrace : WordTrace (prefixWord ++ tailWord_1537357) baseStart_1537357 baseEnd_1537357 := by
    simpa [prefixWord, tailWord_1537357, baseEnd_1537357] using wordTrace_append hprefix tailTrace_1537357
  have hstable : (prefixWord ++ tailWord_1537357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537357).length < 2 ^ (prefixWord ++ tailWord_1537357).sum := by decide
  have hdescent : baseEnd_1537357 < baseStart_1537357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537455 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 9]
def baseStart_1537455 : Nat := 118140960795 + 1537455 * 2 ^ 59
def prefixEnd_1537455 : Nat := 4983230072969 + 3 ^ 40 * 1537455 * 2
def baseEnd_1537455 : Nat := 350868177625949970640835

theorem tailTrace_1537455 : CollatzResearch.WordTrace tailWord_1537455 prefixEnd_1537455 350868177625949970640835 := by
  unfold tailWord_1537455
  simp only [CollatzResearch.WordTrace]
  refine ⟨56075590645070586254333819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37383727096713724169555879 56075590645070586254333819)
  ·
    refine ⟨84113385967605879381500729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56075590645070586254333819 84113385967605879381500729)
    ·
      refine ⟨63085039475704409536125547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84113385967605879381500729 63085039475704409536125547)
      ·
        refine ⟨94627559213556614304188321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63085039475704409536125547 94627559213556614304188321)
        ·
          refine ⟨70970669410167460728141241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94627559213556614304188321 70970669410167460728141241)
          ·
            refine ⟨53228002057625595546105931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70970669410167460728141241 53228002057625595546105931)
            ·
              refine ⟨79842003086438393319158897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53228002057625595546105931 79842003086438393319158897)
              ·
                refine ⟨59881502314828794989369173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79842003086438393319158897 59881502314828794989369173)
                ·
                  refine ⟨350868177625949970640835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59881502314828794989369173 350868177625949970640835)
                  ·
                    rfl

theorem cell21_1537455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_1537455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537455 prefixEnd_1537455 := by exact prefixLift 1537455
  have htrace : WordTrace (prefixWord ++ tailWord_1537455) baseStart_1537455 baseEnd_1537455 := by
    simpa [prefixWord, tailWord_1537455, baseEnd_1537455] using wordTrace_append hprefix tailTrace_1537455
  have hstable : (prefixWord ++ tailWord_1537455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537455).length < 2 ^ (prefixWord ++ tailWord_1537455).sum := by decide
  have hdescent : baseEnd_1537455 < baseStart_1537455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537520 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 4]
def baseStart_1537520 : Nat := 118140960795 + 1537520 * 2 ^ 59
def prefixEnd_1537520 : Nat := 4983230072969 + 3 ^ 40 * 1537520 * 2
def baseEnd_1537520 : Nat := 350883011511524302057369

theorem tailTrace_1537520 : CollatzResearch.WordTrace tailWord_1537520 prefixEnd_1537520 350883011511524302057369 := by
  unfold tailWord_1537520
  simp only [CollatzResearch.WordTrace]
  refine ⟨28038980694917551177725007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37385307593223401570300009 28038980694917551177725007)
  ·
    refine ⟨42058471042376326766587511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28038980694917551177725007 42058471042376326766587511)
    ·
      refine ⟨63087706563564490149881267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42058471042376326766587511 63087706563564490149881267)
      ·
        refine ⟨94631559845346735224821901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63087706563564490149881267 94631559845346735224821901)
        ·
          refine ⟨35486834942005025709308213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94631559845346735224821901 35486834942005025709308213)
          ·
            refine ⟨3326890775812971160247645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35486834942005025709308213 3326890775812971160247645)
            ·
              refine ⟨1247584040929864185092867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3326890775812971160247645 1247584040929864185092867)
              ·
                refine ⟨1871376061394796277639301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247584040929864185092867 1871376061394796277639301)
                ·
                  refine ⟨350883011511524302057369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871376061394796277639301 350883011511524302057369)
                  ·
                    rfl

theorem cell21_1537520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_1537520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537520 prefixEnd_1537520 := by exact prefixLift 1537520
  have htrace : WordTrace (prefixWord ++ tailWord_1537520) baseStart_1537520 baseEnd_1537520 := by
    simpa [prefixWord, tailWord_1537520, baseEnd_1537520] using wordTrace_append hprefix tailTrace_1537520
  have hstable : (prefixWord ++ tailWord_1537520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537520).length < 2 ^ (prefixWord ++ tailWord_1537520).sum := by decide
  have hdescent : baseEnd_1537520 < baseStart_1537520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537540 : List Nat := [2, 3, 2, 3, 3, 1, 1, 3, 3]
def baseStart_1537540 : Nat := 118140960795 + 1537540 * 2 ^ 59
def prefixEnd_1537540 : Nat := 4983230072969 + 3 ^ 40 * 1537540 * 2
def baseEnd_1537540 : Nat := 350887575784008711723995

theorem tailTrace_1537540 : CollatzResearch.WordTrace tailWord_1537540 prefixEnd_1537540 350887575784008711723995 := by
  unfold tailWord_1537540
  simp only [CollatzResearch.WordTrace]
  refine ⟨28039345424881322885589037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37385793899841763847452049 28039345424881322885589037)
  ·
    refine ⟨10514754534330496082095889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28039345424881322885589037 10514754534330496082095889)
    ·
      refine ⟨7886065900747872061571917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10514754534330496082095889 7886065900747872061571917)
      ·
        refine ⟨2957274712780452023089469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7886065900747872061571917 2957274712780452023089469)
        ·
          refine ⟨1108978017292669508658551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2957274712780452023089469 1108978017292669508658551)
          ·
            refine ⟨1663467025939004262987827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108978017292669508658551 1663467025939004262987827)
            ·
              refine ⟨2495200538908506394481741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663467025939004262987827 2495200538908506394481741)
              ·
                refine ⟨935700202090689897930653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2495200538908506394481741 935700202090689897930653)
                ·
                  refine ⟨350887575784008711723995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935700202090689897930653 350887575784008711723995)
                  ·
                    rfl

theorem cell21_1537540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_1537540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537540 prefixEnd_1537540 := by exact prefixLift 1537540
  have htrace : WordTrace (prefixWord ++ tailWord_1537540) baseStart_1537540 baseEnd_1537540 := by
    simpa [prefixWord, tailWord_1537540, baseEnd_1537540] using wordTrace_append hprefix tailTrace_1537540
  have hstable : (prefixWord ++ tailWord_1537540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537540).length < 2 ^ (prefixWord ++ tailWord_1537540).sum := by decide
  have hdescent : baseEnd_1537540 < baseStart_1537540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537593 : List Nat := [1, 2, 1, 5, 1, 2, 2, 7]
def baseStart_1537593 : Nat := 118140960795 + 1537593 * 2 ^ 59
def prefixEnd_1537593 : Nat := 4983230072969 + 3 ^ 40 * 1537593 * 2
def baseEnd_1537593 : Nat := 116966557035364132446851

theorem tailTrace_1537593 : CollatzResearch.WordTrace tailWord_1537593 prefixEnd_1537593 116966557035364132446851 := by
  unfold tailWord_1537593
  simp only [CollatzResearch.WordTrace]
  refine ⟨56080623918570635822857433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37387082612380423881904955 56080623918570635822857433)
  ·
    refine ⟨42060467938927976867143075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56080623918570635822857433 42060467938927976867143075)
    ·
      refine ⟨63090701908391965300714613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42060467938927976867143075 63090701908391965300714613)
      ·
        refine ⟨5914753303911746746941995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63090701908391965300714613 5914753303911746746941995)
        ·
          refine ⟨8872129955867620120412993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5914753303911746746941995 8872129955867620120412993)
          ·
            refine ⟨6654097466900715090309745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8872129955867620120412993 6654097466900715090309745)
            ·
              refine ⟨4990573100175536317732309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6654097466900715090309745 4990573100175536317732309)
              ·
                refine ⟨116966557035364132446851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4990573100175536317732309 116966557035364132446851)
                ·
                  rfl

theorem cell21_1537593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 7].length) (baseStart_1537593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537593 prefixEnd_1537593 := by exact prefixLift 1537593
  have htrace : WordTrace (prefixWord ++ tailWord_1537593) baseStart_1537593 baseEnd_1537593 := by
    simpa [prefixWord, tailWord_1537593, baseEnd_1537593] using wordTrace_append hprefix tailTrace_1537593
  have hstable : (prefixWord ++ tailWord_1537593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537593).length < 2 ^ (prefixWord ++ tailWord_1537593).sum := by decide
  have hdescent : baseEnd_1537593 < baseStart_1537593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537613 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1537613 : Nat := 118140960795 + 1537613 * 2 ^ 59
def prefixEnd_1537613 : Nat := 4983230072969 + 3 ^ 40 * 1537613 * 2
def baseEnd_1537613 : Nat := 350904235378576807007179

theorem tailTrace_1537613 : CollatzResearch.WordTrace tailWord_1537613 prefixEnd_1537613 350904235378576807007179 := by
  unfold tailWord_1537613
  simp only [CollatzResearch.WordTrace]
  refine ⟨56081353378498179238585493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37387568918998786159056995 56081353378498179238585493)
  ·
    refine ⟨2628813439617102151808695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56081353378498179238585493 2628813439617102151808695)
    ·
      refine ⟨3943220159425653227713043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2628813439617102151808695 3943220159425653227713043)
      ·
        refine ⟨5914830239138479841569565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3943220159425653227713043 5914830239138479841569565)
        ·
          refine ⟨2218061339676929940588587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5914830239138479841569565 2218061339676929940588587)
          ·
            refine ⟨3327092009515394910882881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218061339676929940588587 3327092009515394910882881)
            ·
              refine ⟨2495319007136546183162161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3327092009515394910882881 2495319007136546183162161)
              ·
                refine ⟨1871489255352409637371621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2495319007136546183162161 1871489255352409637371621)
                ·
                  refine ⟨350904235378576807007179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871489255352409637371621 350904235378576807007179)
                  ·
                    rfl

theorem cell21_1537613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1537613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537613 prefixEnd_1537613 := by exact prefixLift 1537613
  have htrace : WordTrace (prefixWord ++ tailWord_1537613) baseStart_1537613 baseEnd_1537613 := by
    simpa [prefixWord, tailWord_1537613, baseEnd_1537613] using wordTrace_append hprefix tailTrace_1537613
  have hstable : (prefixWord ++ tailWord_1537613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537613).length < 2 ^ (prefixWord ++ tailWord_1537613).sum := by decide
  have hdescent : baseEnd_1537613 < baseStart_1537613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537672 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 6]
def baseStart_1537672 : Nat := 118140960795 + 1537672 * 2 ^ 59
def prefixEnd_1537672 : Nat := 4983230072969 + 3 ^ 40 * 1537672 * 2
def baseEnd_1537672 : Nat := 350917699982405815523725

theorem tailTrace_1537672 : CollatzResearch.WordTrace tailWord_1537672 prefixEnd_1537672 350917699982405815523725 := by
  unfold tailWord_1537672
  simp only [CollatzResearch.WordTrace]
  refine ⟨28041752642642216157491635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37389003523522954876655513 28041752642642216157491635)
  ·
    refine ⟨42062628963963324236237453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28041752642642216157491635 42062628963963324236237453)
    ·
      refine ⟨15773485861486246588589045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42062628963963324236237453 15773485861486246588589045)
      ·
        refine ⟨1478764299514335617680223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15773485861486246588589045 1478764299514335617680223)
        ·
          refine ⟨2218146449271503426520335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478764299514335617680223 2218146449271503426520335)
          ·
            refine ⟨3327219673907255139780503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218146449271503426520335 3327219673907255139780503)
            ·
              refine ⟨4990829510860882709670755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327219673907255139780503 4990829510860882709670755)
              ·
                refine ⟨7486244266291324064506133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4990829510860882709670755 7486244266291324064506133)
                ·
                  refine ⟨350917699982405815523725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7486244266291324064506133 350917699982405815523725)
                  ·
                    rfl

theorem cell21_1537672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_1537672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537672 prefixEnd_1537672 := by exact prefixLift 1537672
  have htrace : WordTrace (prefixWord ++ tailWord_1537672) baseStart_1537672 baseEnd_1537672 := by
    simpa [prefixWord, tailWord_1537672, baseEnd_1537672] using wordTrace_append hprefix tailTrace_1537672
  have hstable : (prefixWord ++ tailWord_1537672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537672).length < 2 ^ (prefixWord ++ tailWord_1537672).sum := by decide
  have hdescent : baseEnd_1537672 < baseStart_1537672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537700 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_1537700 : Nat := 118140960795 + 1537700 * 2 ^ 59
def prefixEnd_1537700 : Nat := 4983230072969 + 3 ^ 40 * 1537700 * 2
def baseEnd_1537700 : Nat := 350924089963883989057001

theorem tailTrace_1537700 : CollatzResearch.WordTrace tailWord_1537700 prefixEnd_1537700 350924089963883989057001 := by
  unfold tailWord_1537700
  simp only [CollatzResearch.WordTrace]
  refine ⟨28042263264591496548501277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37389684352788662064668369 28042263264591496548501277)
  ·
    refine ⟨10515848724221811205687979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28042263264591496548501277 10515848724221811205687979)
    ·
      refine ⟨15773773086332716808531969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10515848724221811205687979 15773773086332716808531969)
      ·
        refine ⟨11830329814749537606398977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15773773086332716808531969 11830329814749537606398977)
        ·
          refine ⟨8872747361062153204799233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11830329814749537606398977 8872747361062153204799233)
          ·
            refine ⟨6654560520796614903599425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8872747361062153204799233 6654560520796614903599425)
            ·
              refine ⟨4990920390597461177699569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6654560520796614903599425 4990920390597461177699569)
              ·
                refine ⟨3743190292948095883274677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4990920390597461177699569 3743190292948095883274677)
                ·
                  refine ⟨350924089963883989057001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3743190292948095883274677 350924089963883989057001)
                  ·
                    rfl

theorem cell21_1537700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_1537700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537700 prefixEnd_1537700 := by exact prefixLift 1537700
  have htrace : WordTrace (prefixWord ++ tailWord_1537700) baseStart_1537700 baseEnd_1537700 := by
    simpa [prefixWord, tailWord_1537700, baseEnd_1537700] using wordTrace_append hprefix tailTrace_1537700
  have hstable : (prefixWord ++ tailWord_1537700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537700).length < 2 ^ (prefixWord ++ tailWord_1537700).sum := by decide
  have hdescent : baseEnd_1537700 < baseStart_1537700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537714 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_1537714 : Nat := 118140960795 + 1537714 * 2 ^ 59
def prefixEnd_1537714 : Nat := 4983230072969 + 3 ^ 40 * 1537714 * 2
def baseEnd_1537714 : Nat := 350927284954623075823639

theorem tailTrace_1537714 : CollatzResearch.WordTrace tailWord_1537714 prefixEnd_1537714 350927284954623075823639 := by
  unfold tailWord_1537714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14021259287783068372003049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37390024767421515658674797 14021259287783068372003049)
  ·
    refine ⟨10515944465837301279002287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14021259287783068372003049 10515944465837301279002287)
    ·
      refine ⟨15773916698755951918503431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10515944465837301279002287 15773916698755951918503431)
      ·
        refine ⟨23660875048133927877755147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15773916698755951918503431 23660875048133927877755147)
        ·
          refine ⟨35491312572200891816632721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23660875048133927877755147 35491312572200891816632721)
          ·
            refine ⟨26618484429150668862474541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35491312572200891816632721 26618484429150668862474541)
            ·
              refine ⟨9981931660931500823427953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26618484429150668862474541 9981931660931500823427953)
              ·
                refine ⟨7486448745698625617570965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9981931660931500823427953 7486448745698625617570965)
                ·
                  refine ⟨350927284954623075823639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7486448745698625617570965 350927284954623075823639)
                  ·
                    rfl

theorem cell21_1537714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_1537714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537714 prefixEnd_1537714 := by exact prefixLift 1537714
  have htrace : WordTrace (prefixWord ++ tailWord_1537714) baseStart_1537714 baseEnd_1537714 := by
    simpa [prefixWord, tailWord_1537714, baseEnd_1537714] using wordTrace_append hprefix tailTrace_1537714
  have hstable : (prefixWord ++ tailWord_1537714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537714).length < 2 ^ (prefixWord ++ tailWord_1537714).sum := by decide
  have hdescent : baseEnd_1537714 < baseStart_1537714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537745 : List Nat := [1, 2, 2, 1, 2, 5, 2, 6]
def baseStart_1537745 : Nat := 118140960795 + 1537745 * 2 ^ 59
def prefixEnd_1537745 : Nat := 4983230072969 + 3 ^ 40 * 1537745 * 2
def baseEnd_1537745 : Nat := 116978119858991303602303

theorem tailTrace_1537745 : CollatzResearch.WordTrace tailWord_1537745 prefixEnd_1537745 116978119858991303602303 := by
  unfold tailWord_1537745
  simp only [CollatzResearch.WordTrace]
  refine ⟨56086167814019965782390689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37390778542679977188260459 56086167814019965782390689)
  ·
    refine ⟨42064625860514974336793017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56086167814019965782390689 42064625860514974336793017)
    ·
      refine ⟨31548469395386230752594763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42064625860514974336793017 31548469395386230752594763)
      ·
        refine ⟨47322704093079346128892145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31548469395386230752594763 47322704093079346128892145)
        ·
          refine ⟨35492028069809509596669109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47322704093079346128892145 35492028069809509596669109)
          ·
            refine ⟨3327377631544641524687729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35492028069809509596669109 3327377631544641524687729)
            ·
              refine ⟨2495533223658481143515797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3327377631544641524687729 2495533223658481143515797)
              ·
                refine ⟨116978119858991303602303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2495533223658481143515797 116978119858991303602303)
                ·
                  rfl

theorem cell21_1537745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 6].length) (baseStart_1537745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537745 prefixEnd_1537745 := by exact prefixLift 1537745
  have htrace : WordTrace (prefixWord ++ tailWord_1537745) baseStart_1537745 baseEnd_1537745 := by
    simpa [prefixWord, tailWord_1537745, baseEnd_1537745] using wordTrace_append hprefix tailTrace_1537745
  have hstable : (prefixWord ++ tailWord_1537745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537745).length < 2 ^ (prefixWord ++ tailWord_1537745).sum := by decide
  have hdescent : baseEnd_1537745 < baseStart_1537745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537748 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1537748 : Nat := 118140960795 + 1537748 * 2 ^ 59
def prefixEnd_1537748 : Nat := 4983230072969 + 3 ^ 40 * 1537748 * 2
def baseEnd_1537748 : Nat := 350935044217846572256903

theorem tailTrace_1537748 : CollatzResearch.WordTrace tailWord_1537748 prefixEnd_1537748 350935044217846572256903 := by
  unfold tailWord_1537748
  simp only [CollatzResearch.WordTrace]
  refine ⟨28043138616504548647374949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37390851488672731529833265 28043138616504548647374949)
  ·
    refine ⟨5258088490594602871382803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28043138616504548647374949 5258088490594602871382803)
    ·
      refine ⟨7887132735891904307074205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5258088490594602871382803 7887132735891904307074205)
      ·
        refine ⟨2957674775959464115152827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7887132735891904307074205 2957674775959464115152827)
        ·
          refine ⟨4436512163939196172729241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957674775959464115152827 4436512163939196172729241)
          ·
            refine ⟨3327384122954397129546931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4436512163939196172729241 3327384122954397129546931)
            ·
              refine ⟨4991076184431595694320397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327384122954397129546931 4991076184431595694320397)
              ·
                refine ⟨1871653569161848385370149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4991076184431595694320397 1871653569161848385370149)
                ·
                  refine ⟨350935044217846572256903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871653569161848385370149 350935044217846572256903)
                  ·
                    rfl

theorem cell21_1537748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1537748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537748 prefixEnd_1537748 := by exact prefixLift 1537748
  have htrace : WordTrace (prefixWord ++ tailWord_1537748) baseStart_1537748 baseEnd_1537748 := by
    simpa [prefixWord, tailWord_1537748, baseEnd_1537748] using wordTrace_append hprefix tailTrace_1537748
  have hstable : (prefixWord ++ tailWord_1537748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537748).length < 2 ^ (prefixWord ++ tailWord_1537748).sum := by decide
  have hdescent : baseEnd_1537748 < baseStart_1537748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537759 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 7]
def baseStart_1537759 : Nat := 118140960795 + 1537759 * 2 ^ 59
def prefixEnd_1537759 : Nat := 4983230072969 + 3 ^ 40 * 1537759 * 2
def baseEnd_1537759 : Nat := 350937554567712997573547

theorem tailTrace_1537759 : CollatzResearch.WordTrace tailWord_1537759 prefixEnd_1537759 350937554567712997573547 := by
  unfold tailWord_1537759
  simp only [CollatzResearch.WordTrace]
  refine ⟨56086678435969246173400331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37391118957312830782266887 56086678435969246173400331)
  ·
    refine ⟨84130017653953869260100497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56086678435969246173400331 84130017653953869260100497)
    ·
      refine ⟨63097513240465401945075373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84130017653953869260100497 63097513240465401945075373)
      ·
        refine ⟨23661567465174525729403265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63097513240465401945075373 23661567465174525729403265)
        ·
          refine ⟨17746175598880894297052449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23661567465174525729403265 17746175598880894297052449)
          ·
            refine ⟨13309631699160670722789337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17746175598880894297052449 13309631699160670722789337)
            ·
              refine ⟨9982223774370503042092003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13309631699160670722789337 9982223774370503042092003)
              ·
                refine ⟨14973335661555754563138005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9982223774370503042092003 14973335661555754563138005)
                ·
                  refine ⟨350937554567712997573547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14973335661555754563138005 350937554567712997573547)
                  ·
                    rfl

theorem cell21_1537759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_1537759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537759 prefixEnd_1537759 := by exact prefixLift 1537759
  have htrace : WordTrace (prefixWord ++ tailWord_1537759) baseStart_1537759 baseEnd_1537759 := by
    simpa [prefixWord, tailWord_1537759, baseEnd_1537759] using wordTrace_append hprefix tailTrace_1537759
  have hstable : (prefixWord ++ tailWord_1537759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537759).length < 2 ^ (prefixWord ++ tailWord_1537759).sum := by decide
  have hdescent : baseEnd_1537759 < baseStart_1537759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537838 : List Nat := [4, 1, 3, 2, 2, 1, 8]
def baseStart_1537838 : Nat := 118140960795 + 1537838 * 2 ^ 59
def prefixEnd_1537838 : Nat := 4983230072969 + 3 ^ 40 * 1537838 * 2
def baseEnd_1537838 : Nat := 38995064827114046195191

theorem tailTrace_1537838 : CollatzResearch.WordTrace tailWord_1537838 prefixEnd_1537838 38995064827114046195191 := by
  unfold tailWord_1537838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011194975335380333190771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37393039868455361777017445 7011194975335380333190771)
  ·
    refine ⟨10516792463003070499786157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7011194975335380333190771 10516792463003070499786157)
    ·
      refine ⟨3943797173626151437419809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10516792463003070499786157 3943797173626151437419809)
      ·
        refine ⟨2957847880219613578064857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3943797173626151437419809 2957847880219613578064857)
        ·
          refine ⟨2218385910164710183548643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2957847880219613578064857 2218385910164710183548643)
          ·
            refine ⟨3327578865247065275322965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218385910164710183548643 3327578865247065275322965)
            ·
              refine ⟨38995064827114046195191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3327578865247065275322965 38995064827114046195191)
              ·
                rfl

theorem cell21_1537838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 8].length) (baseStart_1537838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537838 prefixEnd_1537838 := by exact prefixLift 1537838
  have htrace : WordTrace (prefixWord ++ tailWord_1537838) baseStart_1537838 baseEnd_1537838 := by
    simpa [prefixWord, tailWord_1537838, baseEnd_1537838] using wordTrace_append hprefix tailTrace_1537838
  have hstable : (prefixWord ++ tailWord_1537838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537838).length < 2 ^ (prefixWord ++ tailWord_1537838).sum := by decide
  have hdescent : baseEnd_1537838 < baseStart_1537838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537869 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1537869 : Nat := 118140960795 + 1537869 * 2 ^ 59
def prefixEnd_1537869 : Nat := 4983230072969 + 3 ^ 40 * 1537869 * 2
def baseEnd_1537869 : Nat := 350962658066377250739989

theorem tailTrace_1537869 : CollatzResearch.WordTrace tailWord_1537869 prefixEnd_1537869 350962658066377250739989 := by
  unfold tailWord_1537869
  simp only [CollatzResearch.WordTrace]
  refine ⟨56090690465570734959904661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37393793643713823306603107 56090690465570734959904661)
  ·
    refine ⟨2629251115573628201245531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56090690465570734959904661 2629251115573628201245531)
    ·
      refine ⟨3943876673360442301868297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2629251115573628201245531 3943876673360442301868297)
      ·
        refine ⟨2957907505020331726401223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3943876673360442301868297 2957907505020331726401223)
        ·
          refine ⟨4436861257530497589601835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957907505020331726401223 4436861257530497589601835)
          ·
            refine ⟨6655291886295746384402753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436861257530497589601835 6655291886295746384402753)
            ·
              refine ⟨4991468914721809788302065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6655291886295746384402753 4991468914721809788302065)
              ·
                refine ⟨3743601686041357341226549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4991468914721809788302065 3743601686041357341226549)
                ·
                  refine ⟨350962658066377250739989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3743601686041357341226549 350962658066377250739989)
                  ·
                    rfl

theorem cell21_1537869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1537869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537869 prefixEnd_1537869 := by exact prefixLift 1537869
  have htrace : WordTrace (prefixWord ++ tailWord_1537869) baseStart_1537869 baseEnd_1537869 := by
    simpa [prefixWord, tailWord_1537869, baseEnd_1537869] using wordTrace_append hprefix tailTrace_1537869
  have hstable : (prefixWord ++ tailWord_1537869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537869).length < 2 ^ (prefixWord ++ tailWord_1537869).sum := by decide
  have hdescent : baseEnd_1537869 < baseStart_1537869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537956 : List Nat := [2, 3, 1, 2, 1, 12]
def baseStart_1537956 : Nat := 118140960795 + 1537956 * 2 ^ 59
def prefixEnd_1537956 : Nat := 4983230072969 + 3 ^ 40 * 1537956 * 2
def baseEnd_1537956 : Nat := 12999352320432756769993

theorem tailTrace_1537956 : CollatzResearch.WordTrace tailWord_1537956 prefixEnd_1537956 12999352320432756769993 := by
  unfold tailWord_1537956
  simp only [CollatzResearch.WordTrace]
  refine ⟨28046931808127774409160861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37395909077503699212214481 28046931808127774409160861)
  ·
    refine ⟨10517599428047915403435323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28046931808127774409160861 10517599428047915403435323)
    ·
      refine ⟨15776399142071873105152985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10517599428047915403435323 15776399142071873105152985)
      ·
        refine ⟨11832299356553904828864739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15776399142071873105152985 11832299356553904828864739)
        ·
          refine ⟨17748449034830857243297109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11832299356553904828864739 17748449034830857243297109)
          ·
            refine ⟨12999352320432756769993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17748449034830857243297109 12999352320432756769993)
            ·
              rfl

theorem cell21_1537956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 12].length) (baseStart_1537956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537956 prefixEnd_1537956 := by exact prefixLift 1537956
  have htrace : WordTrace (prefixWord ++ tailWord_1537956) baseStart_1537956 baseEnd_1537956 := by
    simpa [prefixWord, tailWord_1537956, baseEnd_1537956] using wordTrace_append hprefix tailTrace_1537956
  have hstable : (prefixWord ++ tailWord_1537956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537956).length < 2 ^ (prefixWord ++ tailWord_1537956).sum := by decide
  have hdescent : baseEnd_1537956 < baseStart_1537956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537959 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 4]
def baseStart_1537959 : Nat := 118140960795 + 1537959 * 2 ^ 59
def prefixEnd_1537959 : Nat := 4983230072969 + 3 ^ 40 * 1537959 * 2
def baseEnd_1537959 : Nat := 350983197292557094239805

theorem tailTrace_1537959 : CollatzResearch.WordTrace tailWord_1537959 prefixEnd_1537959 350983197292557094239805 := by
  unfold tailWord_1537959
  simp only [CollatzResearch.WordTrace]
  refine ⟨56093973035244680330680931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37395982023496453553787287 56093973035244680330680931)
  ·
    refine ⟨84140959552867020496021397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56093973035244680330680931 84140959552867020496021397)
    ·
      refine ⟨3944107479040641585751003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84140959552867020496021397 3944107479040641585751003)
      ·
        refine ⟨5916161218560962378626505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3944107479040641585751003 5916161218560962378626505)
        ·
          refine ⟨4437120913920721783969879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5916161218560962378626505 4437120913920721783969879)
          ·
            refine ⟨6655681370881082675954819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437120913920721783969879 6655681370881082675954819)
            ·
              refine ⟨9983522056321624013932229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6655681370881082675954819 9983522056321624013932229)
              ·
                refine ⟨1871910385560304502612293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9983522056321624013932229 1871910385560304502612293)
                ·
                  refine ⟨350983197292557094239805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871910385560304502612293 350983197292557094239805)
                  ·
                    rfl

theorem cell21_1537959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 4].length) (baseStart_1537959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537959 prefixEnd_1537959 := by exact prefixLift 1537959
  have htrace : WordTrace (prefixWord ++ tailWord_1537959) baseStart_1537959 baseEnd_1537959 := by
    simpa [prefixWord, tailWord_1537959, baseEnd_1537959] using wordTrace_append hprefix tailTrace_1537959
  have hstable : (prefixWord ++ tailWord_1537959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537959).length < 2 ^ (prefixWord ++ tailWord_1537959).sum := by decide
  have hdescent : baseEnd_1537959 < baseStart_1537959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537973 : List Nat := [1, 3, 3, 2, 1, 2, 3, 6]
def baseStart_1537973 : Nat := 118140960795 + 1537973 * 2 ^ 59
def prefixEnd_1537973 : Nat := 4983230072969 + 3 ^ 40 * 1537973 * 2
def baseEnd_1537973 : Nat := 116995464094432060335481

theorem tailTrace_1537973 : CollatzResearch.WordTrace tailWord_1537973 prefixEnd_1537973 116995464094432060335481 := by
  unfold tailWord_1537973
  simp only [CollatzResearch.WordTrace]
  refine ⟨56094483657193960721690573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37396322438129307147793715 56094483657193960721690573)
  ·
    refine ⟨21035431371447735270633965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56094483657193960721690573 21035431371447735270633965)
    ·
      refine ⟨7888286764292900726487737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21035431371447735270633965 7888286764292900726487737)
      ·
        refine ⟨5916215073219675544865803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7888286764292900726487737 5916215073219675544865803)
        ·
          refine ⟨8874322609829513317298705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5916215073219675544865803 8874322609829513317298705)
          ·
            refine ⟨6655741957372134987974029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8874322609829513317298705 6655741957372134987974029)
            ·
              refine ⟨2495903234014550620490261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6655741957372134987974029 2495903234014550620490261)
              ·
                refine ⟨116995464094432060335481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2495903234014550620490261 116995464094432060335481)
                ·
                  rfl

theorem cell21_1537973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 6].length) (baseStart_1537973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1537973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1537973 prefixEnd_1537973 := by exact prefixLift 1537973
  have htrace : WordTrace (prefixWord ++ tailWord_1537973) baseStart_1537973 baseEnd_1537973 := by
    simpa [prefixWord, tailWord_1537973, baseEnd_1537973] using wordTrace_append hprefix tailTrace_1537973
  have hstable : (prefixWord ++ tailWord_1537973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537973).length < 2 ^ (prefixWord ++ tailWord_1537973).sum := by decide
  have hdescent : baseEnd_1537973 < baseStart_1537973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538108 : List Nat := [2, 2, 2, 2, 2, 1, 1, 9]
def baseStart_1538108 : Nat := 118140960795 + 1538108 * 2 ^ 59
def prefixEnd_1538108 : Nat := 4983230072969 + 3 ^ 40 * 1538108 * 2
def baseEnd_1538108 : Nat := 117005733707521982085389

theorem tailTrace_1538108 : CollatzResearch.WordTrace tailWord_1538108 prefixEnd_1538108 117005733707521982085389 := by
  unfold tailWord_1538108
  simp only [CollatzResearch.WordTrace]
  refine ⟨28049703755852439388927489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37399605007803252518569985 28049703755852439388927489)
  ·
    refine ⟨21037277816889329541695617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28049703755852439388927489 21037277816889329541695617)
    ·
      refine ⟨15777958362666997156271713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21037277816889329541695617 15777958362666997156271713)
      ·
        refine ⟨11833468772000247867203785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15777958362666997156271713 11833468772000247867203785)
        ·
          refine ⟨8875101579000185900402839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11833468772000247867203785 8875101579000185900402839)
          ·
            refine ⟨13312652368500278850604259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8875101579000185900402839 13312652368500278850604259)
            ·
              refine ⟨19968978552750418275906389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13312652368500278850604259 19968978552750418275906389)
              ·
                refine ⟨117005733707521982085389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19968978552750418275906389 117005733707521982085389)
                ·
                  rfl

theorem cell21_1538108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_1538108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538108 prefixEnd_1538108 := by exact prefixLift 1538108
  have htrace : WordTrace (prefixWord ++ tailWord_1538108) baseStart_1538108 baseEnd_1538108 := by
    simpa [prefixWord, tailWord_1538108, baseEnd_1538108] using wordTrace_append hprefix tailTrace_1538108
  have hstable : (prefixWord ++ tailWord_1538108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538108).length < 2 ^ (prefixWord ++ tailWord_1538108).sum := by decide
  have hdescent : baseEnd_1538108 < baseStart_1538108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538173 : List Nat := [1, 4, 1, 1, 3, 3, 2, 3, 3]
def baseStart_1538173 : Nat := 118140960795 + 1538173 * 2 ^ 59
def prefixEnd_1538173 : Nat := 4983230072969 + 3 ^ 40 * 1538173 * 2
def baseEnd_1538173 : Nat := 351032035008140277672701

theorem tailTrace_1538173 : CollatzResearch.WordTrace tailWord_1538173 prefixEnd_1538173 351032035008140277672701 := by
  unfold tailWord_1538173
  simp only [CollatzResearch.WordTrace]
  refine ⟨56101778256469394878971173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37401185504312929919314115 56101778256469394878971173)
  ·
    refine ⟨10519083423088011539807095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56101778256469394878971173 10519083423088011539807095)
    ·
      refine ⟨15778625134632017309710643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10519083423088011539807095 15778625134632017309710643)
      ·
        refine ⟨23667937701948025964565965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15778625134632017309710643 23667937701948025964565965)
        ·
          refine ⟨8875476638230509736712237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23667937701948025964565965 8875476638230509736712237)
          ·
            refine ⟨3328303739336441151267089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8875476638230509736712237 3328303739336441151267089)
            ·
              refine ⟨2496227804502330863450317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3328303739336441151267089 2496227804502330863450317)
              ·
                refine ⟨936085426688374073793869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2496227804502330863450317 936085426688374073793869)
                ·
                  refine ⟨351032035008140277672701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936085426688374073793869 351032035008140277672701)
                  ·
                    rfl

theorem cell21_1538173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_1538173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538173 prefixEnd_1538173 := by exact prefixLift 1538173
  have htrace : WordTrace (prefixWord ++ tailWord_1538173) baseStart_1538173 baseEnd_1538173 := by
    simpa [prefixWord, tailWord_1538173, baseEnd_1538173] using wordTrace_append hprefix tailTrace_1538173
  have hstable : (prefixWord ++ tailWord_1538173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538173).length < 2 ^ (prefixWord ++ tailWord_1538173).sum := by decide
  have hdescent : baseEnd_1538173 < baseStart_1538173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538218 : List Nat := [3, 1, 5, 1, 2, 1, 1, 7]
def baseStart_1538218 : Nat := 118140960795 + 1538218 * 2 ^ 59
def prefixEnd_1538218 : Nat := 4983230072969 + 3 ^ 40 * 1538218 * 2
def baseEnd_1538218 : Nat := 117014101540410066474203

theorem tailTrace_1538218 : CollatzResearch.WordTrace tailWord_1538218 prefixEnd_1538218 117014101540410066474203 := by
  unfold tailWord_1538218
  simp only [CollatzResearch.WordTrace]
  refine ⟨14025854885326591891089827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37402279694204245042906205 14025854885326591891089827)
  ·
    refine ⟨21038782327989887836634741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14025854885326591891089827 21038782327989887836634741)
    ·
      refine ⟨1972385843249051984684507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21038782327989887836634741 1972385843249051984684507)
      ·
        refine ⟨2958578764873577977026761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972385843249051984684507 2958578764873577977026761)
        ·
          refine ⟨2218934073655183482770071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2958578764873577977026761 2218934073655183482770071)
          ·
            refine ⟨3328401110482775224155107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218934073655183482770071 3328401110482775224155107)
            ·
              refine ⟨4992601665724162836232661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328401110482775224155107 4992601665724162836232661)
              ·
                refine ⟨117014101540410066474203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4992601665724162836232661 117014101540410066474203)
                ·
                  rfl

theorem cell21_1538218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_1538218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538218 prefixEnd_1538218 := by exact prefixLift 1538218
  have htrace : WordTrace (prefixWord ++ tailWord_1538218) baseStart_1538218 baseEnd_1538218 := by
    simpa [prefixWord, tailWord_1538218, baseEnd_1538218] using wordTrace_append hprefix tailTrace_1538218
  have hstable : (prefixWord ++ tailWord_1538218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538218).length < 2 ^ (prefixWord ++ tailWord_1538218).sum := by decide
  have hdescent : baseEnd_1538218 < baseStart_1538218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538311 : List Nat := [1, 1, 4, 5, 2, 1, 1, 6]
def baseStart_1538311 : Nat := 118140960795 + 1538311 * 2 ^ 59
def prefixEnd_1538311 : Nat := 4983230072969 + 3 ^ 40 * 1538311 * 2
def baseEnd_1538311 : Nat := 117021176162760901457473

theorem tailTrace_1538311 : CollatzResearch.WordTrace tailWord_1538311 prefixEnd_1538311 117021176162760901457473 := by
  unfold tailWord_1538311
  simp only [CollatzResearch.WordTrace]
  refine ⟨56106811529969444447494787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37404541019979629631663191 56106811529969444447494787)
  ·
    refine ⟨84160217294954166671242181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56106811529969444447494787 84160217294954166671242181)
    ·
      refine ⟨15780040742803906250857909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84160217294954166671242181 15780040742803906250857909)
      ·
        refine ⟨1479378819637866211017929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15780040742803906250857909 1479378819637866211017929)
        ·
          refine ⟨1109534114728399658263447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1479378819637866211017929 1109534114728399658263447)
          ·
            refine ⟨1664301172092599487395171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109534114728399658263447 1664301172092599487395171)
            ·
              refine ⟨2496451758138899231092757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664301172092599487395171 2496451758138899231092757)
              ·
                refine ⟨117021176162760901457473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2496451758138899231092757 117021176162760901457473)
                ·
                  rfl

theorem cell21_1538311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 6].length) (baseStart_1538311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538311 prefixEnd_1538311 := by exact prefixLift 1538311
  have htrace : WordTrace (prefixWord ++ tailWord_1538311) baseStart_1538311 baseEnd_1538311 := by
    simpa [prefixWord, tailWord_1538311, baseEnd_1538311] using wordTrace_append hprefix tailTrace_1538311
  have hstable : (prefixWord ++ tailWord_1538311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538311).length < 2 ^ (prefixWord ++ tailWord_1538311).sum := by decide
  have hdescent : baseEnd_1538311 < baseStart_1538311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538356 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1538356 : Nat := 118140960795 + 1538356 * 2 ^ 59
def prefixEnd_1538356 : Nat := 4983230072969 + 3 ^ 40 * 1538356 * 2
def baseEnd_1538356 : Nat := 351073798101372626122327

theorem tailTrace_1538356 : CollatzResearch.WordTrace tailWord_1538356 prefixEnd_1538356 351073798101372626122327 := by
  unfold tailWord_1538356
  simp only [CollatzResearch.WordTrace]
  refine ⟨28054226407403208566441461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37405635209870944755255281 28054226407403208566441461)
  ·
    refine ⟨2630083725694050803103887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28054226407403208566441461 2630083725694050803103887)
    ·
      refine ⟨3945125588541076204655831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2630083725694050803103887 3945125588541076204655831)
      ·
        refine ⟨5917688382811614306983747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945125588541076204655831 5917688382811614306983747)
        ·
          refine ⟨8876532574217421460475621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5917688382811614306983747 8876532574217421460475621)
          ·
            refine ⟨1664349857665766523839179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8876532574217421460475621 1664349857665766523839179)
            ·
              refine ⟨2496524786498649785758769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664349857665766523839179 2496524786498649785758769)
              ·
                refine ⟨1872393589873987339319077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496524786498649785758769 1872393589873987339319077)
                ·
                  refine ⟨351073798101372626122327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1872393589873987339319077 351073798101372626122327)
                  ·
                    rfl

theorem cell21_1538356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1538356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538356 prefixEnd_1538356 := by exact prefixLift 1538356
  have htrace : WordTrace (prefixWord ++ tailWord_1538356) baseStart_1538356 baseEnd_1538356 := by
    simpa [prefixWord, tailWord_1538356, baseEnd_1538356] using wordTrace_append hprefix tailTrace_1538356
  have hstable : (prefixWord ++ tailWord_1538356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538356).length < 2 ^ (prefixWord ++ tailWord_1538356).sum := by decide
  have hdescent : baseEnd_1538356 < baseStart_1538356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538367 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 5]
def baseStart_1538367 : Nat := 118140960795 + 1538367 * 2 ^ 59
def prefixEnd_1538367 : Nat := 4983230072969 + 3 ^ 40 * 1538367 * 2
def baseEnd_1538367 : Nat := 351076308451239051438971

theorem tailTrace_1538367 : CollatzResearch.WordTrace tailWord_1538367 prefixEnd_1538367 351076308451239051438971 := by
  unfold tailWord_1538367
  simp only [CollatzResearch.WordTrace]
  refine ⟨56108854017766566011533355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37405902678511044007688903 56108854017766566011533355)
  ·
    refine ⟨84163281026649849017300033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56108854017766566011533355 84163281026649849017300033)
    ·
      refine ⟨63122460769987386762975025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84163281026649849017300033 63122460769987386762975025)
      ·
        refine ⟨47341845577490540072231269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63122460769987386762975025 47341845577490540072231269)
        ·
          refine ⟨8876596045779476263543363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47341845577490540072231269 8876596045779476263543363)
          ·
            refine ⟨13314894068669214395315045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8876596045779476263543363 13314894068669214395315045)
            ·
              refine ⟨2496542637875477699121571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13314894068669214395315045 2496542637875477699121571)
              ·
                refine ⟨3744813956813216548682357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496542637875477699121571 3744813956813216548682357)
                ·
                  refine ⟨351076308451239051438971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3744813956813216548682357 351076308451239051438971)
                  ·
                    rfl

theorem cell21_1538367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 5].length) (baseStart_1538367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538367 prefixEnd_1538367 := by exact prefixLift 1538367
  have htrace : WordTrace (prefixWord ++ tailWord_1538367) baseStart_1538367 baseEnd_1538367 := by
    simpa [prefixWord, tailWord_1538367, baseEnd_1538367] using wordTrace_append hprefix tailTrace_1538367
  have hstable : (prefixWord ++ tailWord_1538367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538367).length < 2 ^ (prefixWord ++ tailWord_1538367).sum := by decide
  have hdescent : baseEnd_1538367 < baseStart_1538367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538536 : List Nat := [2, 1, 4, 1, 1, 3, 2, 4, 3]
def baseStart_1538536 : Nat := 118140960795 + 1538536 * 2 ^ 59
def prefixEnd_1538536 : Nat := 4983230072969 + 3 ^ 40 * 1538536 * 2
def baseEnd_1538536 : Nat := 351114876553732313121959

theorem tailTrace_1538536 : CollatzResearch.WordTrace tailWord_1538536 prefixEnd_1538536 351114876553732313121959 := by
  unfold tailWord_1538536
  simp only [CollatzResearch.WordTrace]
  refine ⟨28057508977077153937217731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37410011969436205249623641 28057508977077153937217731)
  ·
    refine ⟨42086263465615730905826597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28057508977077153937217731 42086263465615730905826597)
    ·
      refine ⟨7891174399802949544842487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42086263465615730905826597 7891174399802949544842487)
      ·
        refine ⟨11836761599704424317263731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7891174399802949544842487 11836761599704424317263731)
        ·
          refine ⟨17755142399556636475895597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11836761599704424317263731 17755142399556636475895597)
          ·
            refine ⟨6658178399833738678460849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17755142399556636475895597 6658178399833738678460849)
            ·
              refine ⟨4993633799875304008845637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6658178399833738678460849 4993633799875304008845637)
              ·
                refine ⟨936306337476619501658557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4993633799875304008845637 936306337476619501658557)
                ·
                  refine ⟨351114876553732313121959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936306337476619501658557 351114876553732313121959)
                  ·
                    rfl

theorem cell21_1538536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 3].length) (baseStart_1538536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538536 prefixEnd_1538536 := by exact prefixLift 1538536
  have htrace : WordTrace (prefixWord ++ tailWord_1538536) baseStart_1538536 baseEnd_1538536 := by
    simpa [prefixWord, tailWord_1538536, baseEnd_1538536] using wordTrace_append hprefix tailTrace_1538536
  have hstable : (prefixWord ++ tailWord_1538536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538536).length < 2 ^ (prefixWord ++ tailWord_1538536).sum := by decide
  have hdescent : baseEnd_1538536 < baseStart_1538536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538547 : List Nat := [1, 1, 1, 2, 2, 2, 4, 8]
def baseStart_1538547 : Nat := 118140960795 + 1538547 * 2 ^ 59
def prefixEnd_1538547 : Nat := 4983230072969 + 3 ^ 40 * 1538547 * 2
def baseEnd_1538547 : Nat := 117039128967866246146201

theorem tailTrace_1538547 : CollatzResearch.WordTrace tailWord_1538547 prefixEnd_1538547 117039128967866246146201 := by
  unfold tailWord_1538547
  simp only [CollatzResearch.WordTrace]
  refine ⟨56115419157114456753085895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37410279438076304502057263 56115419157114456753085895)
  ·
    refine ⟨84173128735671685129628843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56115419157114456753085895 84173128735671685129628843)
    ·
      refine ⟨126259693103507527694443265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84173128735671685129628843 126259693103507527694443265)
      ·
        refine ⟨94694769827630645770832449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126259693103507527694443265 94694769827630645770832449)
        ·
          refine ⟨71021077370722984328124337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94694769827630645770832449 71021077370722984328124337)
          ·
            refine ⟨53265808028042238246093253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71021077370722984328124337 53265808028042238246093253)
            ·
              refine ⟨9987339005257919671142485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53265808028042238246093253 9987339005257919671142485)
              ·
                refine ⟨117039128967866246146201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9987339005257919671142485 117039128967866246146201)
                ·
                  rfl

theorem cell21_1538547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 8].length) (baseStart_1538547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538547 prefixEnd_1538547 := by exact prefixLift 1538547
  have htrace : WordTrace (prefixWord ++ tailWord_1538547) baseStart_1538547 baseEnd_1538547 := by
    simpa [prefixWord, tailWord_1538547, baseEnd_1538547] using wordTrace_append hprefix tailTrace_1538547
  have hstable : (prefixWord ++ tailWord_1538547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538547).length < 2 ^ (prefixWord ++ tailWord_1538547).sum := by decide
  have hdescent : baseEnd_1538547 < baseStart_1538547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538595 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 5]
def baseStart_1538595 : Nat := 118140960795 + 1538595 * 2 ^ 59
def prefixEnd_1538595 : Nat := 4983230072969 + 3 ^ 40 * 1538595 * 2
def baseEnd_1538595 : Nat := 351128341157561321638505

theorem tailTrace_1538595 : CollatzResearch.WordTrace tailWord_1538595 prefixEnd_1538595 351128341157561321638505 := by
  unfold tailWord_1538595
  simp only [CollatzResearch.WordTrace]
  refine ⟨56117169860940560950833239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37411446573960373967222159 56117169860940560950833239)
  ·
    refine ⟨84175754791410841426249859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56117169860940560950833239 84175754791410841426249859)
    ·
      refine ⟨126263632187116262139374789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84175754791410841426249859 126263632187116262139374789)
      ·
        refine ⟨23674431035084299151132773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126263632187116262139374789 23674431035084299151132773)
        ·
          refine ⟨4438955819078306090837395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23674431035084299151132773 4438955819078306090837395)
          ·
            refine ⟨6658433728617459136256093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438955819078306090837395 6658433728617459136256093)
            ·
              refine ⟨2496912648231547176096035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6658433728617459136256093 2496912648231547176096035)
              ·
                refine ⟨3745368972347320764144053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496912648231547176096035 3745368972347320764144053)
                ·
                  refine ⟨351128341157561321638505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3745368972347320764144053 351128341157561321638505)
                  ·
                    rfl

theorem cell21_1538595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 5].length) (baseStart_1538595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538595 prefixEnd_1538595 := by exact prefixLift 1538595
  have htrace : WordTrace (prefixWord ++ tailWord_1538595) baseStart_1538595 baseEnd_1538595 := by
    simpa [prefixWord, tailWord_1538595, baseEnd_1538595] using wordTrace_append hprefix tailTrace_1538595
  have hstable : (prefixWord ++ tailWord_1538595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538595).length < 2 ^ (prefixWord ++ tailWord_1538595).sum := by decide
  have hdescent : baseEnd_1538595 < baseStart_1538595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538623 : List Nat := [1, 1, 2, 2, 3, 2, 1, 9]
def baseStart_1538623 : Nat := 118140960795 + 1538623 * 2 ^ 59
def prefixEnd_1538623 : Nat := 4983230072969 + 3 ^ 40 * 1538623 * 2
def baseEnd_1538623 : Nat := 117044910379679831723927

theorem tailTrace_1538623 : CollatzResearch.WordTrace tailWord_1538623 prefixEnd_1538623 117044910379679831723927 := by
  unfold tailWord_1538623
  simp only [CollatzResearch.WordTrace]
  refine ⟨56118191104839121732852523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37412127403226081155235015 56118191104839121732852523)
  ·
    refine ⟨84177286657258682599278785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56118191104839121732852523 84177286657258682599278785)
    ·
      refine ⟨63132964992944011949459089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84177286657258682599278785 63132964992944011949459089)
      ·
        refine ⟨47349723744708008962094317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63132964992944011949459089 47349723744708008962094317)
        ·
          refine ⟨17756146404265503360785369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47349723744708008962094317 17756146404265503360785369)
          ·
            refine ⟨13317109803199127520589027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17756146404265503360785369 13317109803199127520589027)
            ·
              refine ⟨19975664704798691280883541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13317109803199127520589027 19975664704798691280883541)
              ·
                refine ⟨117044910379679831723927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19975664704798691280883541 117044910379679831723927)
                ·
                  rfl

theorem cell21_1538623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 9].length) (baseStart_1538623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538623 prefixEnd_1538623 := by exact prefixLift 1538623
  have htrace : WordTrace (prefixWord ++ tailWord_1538623) baseStart_1538623 baseEnd_1538623 := by
    simpa [prefixWord, tailWord_1538623, baseEnd_1538623] using wordTrace_append hprefix tailTrace_1538623
  have hstable : (prefixWord ++ tailWord_1538623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538623).length < 2 ^ (prefixWord ++ tailWord_1538623).sum := by decide
  have hdescent : baseEnd_1538623 < baseStart_1538623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538688 : List Nat := [2, 1, 1, 2, 1, 6, 2, 3, 3]
def baseStart_1538688 : Nat := 118140960795 + 1538688 * 2 ^ 59
def prefixEnd_1538688 : Nat := 4983230072969 + 3 ^ 40 * 1538688 * 2
def baseEnd_1538688 : Nat := 351149565024613826588315

theorem tailTrace_1538688 : CollatzResearch.WordTrace tailWord_1538688 prefixEnd_1538688 351149565024613826588315 := by
  unfold tailWord_1538688
  simp only [CollatzResearch.WordTrace]
  refine ⟨28060280924801818916984359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37413707899735758555979145 28060280924801818916984359)
  ·
    refine ⟨42090421387202728375476539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28060280924801818916984359 42090421387202728375476539)
    ·
      refine ⟨63135632080804092563214809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42090421387202728375476539 63135632080804092563214809)
      ·
        refine ⟨47351724060603069422411107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63135632080804092563214809 47351724060603069422411107)
        ·
          refine ⟨71027586090904604133616661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47351724060603069422411107 71027586090904604133616661)
          ·
            refine ⟨3329418098011153318763281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71027586090904604133616661 3329418098011153318763281)
            ·
              refine ⟨2497063573508364989072461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3329418098011153318763281 2497063573508364989072461)
              ·
                refine ⟨936398840065636870902173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2497063573508364989072461 936398840065636870902173)
                ·
                  refine ⟨351149565024613826588315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936398840065636870902173 351149565024613826588315)
                  ·
                    rfl

theorem cell21_1538688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 3].length) (baseStart_1538688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538688 prefixEnd_1538688 := by exact prefixLift 1538688
  have htrace : WordTrace (prefixWord ++ tailWord_1538688) baseStart_1538688 baseEnd_1538688 := by
    simpa [prefixWord, tailWord_1538688, baseEnd_1538688] using wordTrace_append hprefix tailTrace_1538688
  have hstable : (prefixWord ++ tailWord_1538688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538688).length < 2 ^ (prefixWord ++ tailWord_1538688).sum := by decide
  have hdescent : baseEnd_1538688 < baseStart_1538688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538733 : List Nat := [1, 5, 2, 1, 1, 2, 4, 5]
def baseStart_1538733 : Nat := 118140960795 + 1538733 * 2 ^ 59
def prefixEnd_1538733 : Nat := 4983230072969 + 3 ^ 40 * 1538733 * 2
def baseEnd_1538733 : Nat := 117053278212567916112741

theorem tailTrace_1538733 : CollatzResearch.WordTrace tailWord_1538733 prefixEnd_1538733 117053278212567916112741 := by
  unfold tailWord_1538733
  simp only [CollatzResearch.WordTrace]
  refine ⟨56122203134440610519356853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37414802089627073679571235 56122203134440610519356853)
  ·
    refine ⟨5261456543853807236189705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56122203134440610519356853 5261456543853807236189705)
    ·
      refine ⟨3946092407890355427142279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5261456543853807236189705 3946092407890355427142279)
      ·
        refine ⟨5919138611835533140713419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3946092407890355427142279 5919138611835533140713419)
        ·
          refine ⟨8878707917753299711070129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5919138611835533140713419 8878707917753299711070129)
          ·
            refine ⟨6659030938314974783302597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8878707917753299711070129 6659030938314974783302597)
            ·
              refine ⟨1248568300934057771869237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6659030938314974783302597 1248568300934057771869237)
              ·
                refine ⟨117053278212567916112741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1248568300934057771869237 117053278212567916112741)
                ·
                  rfl

theorem cell21_1538733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 5].length) (baseStart_1538733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538733 prefixEnd_1538733 := by exact prefixLift 1538733
  have htrace : WordTrace (prefixWord ++ tailWord_1538733) baseStart_1538733 baseEnd_1538733 := by
    simpa [prefixWord, tailWord_1538733, baseEnd_1538733] using wordTrace_append hprefix tailTrace_1538733
  have hstable : (prefixWord ++ tailWord_1538733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538733).length < 2 ^ (prefixWord ++ tailWord_1538733).sum := by decide
  have hdescent : baseEnd_1538733 < baseStart_1538733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538764 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 5]
def baseStart_1538764 : Nat := 118140960795 + 1538764 * 2 ^ 59
def prefixEnd_1538764 : Nat := 4983230072969 + 3 ^ 40 * 1538764 * 2
def baseEnd_1538764 : Nat := 351166909260054583321493

theorem tailTrace_1538764 : CollatzResearch.WordTrace tailWord_1538764 prefixEnd_1538764 351166909260054583321493 := by
  unfold tailWord_1538764
  simp only [CollatzResearch.WordTrace]
  refine ⟨28061666898664151406867673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37415555864885535209156897 28061666898664151406867673)
  ·
    refine ⟨21046250173998113555150755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28061666898664151406867673 21046250173998113555150755)
    ·
      refine ⟨31569375260997170332726133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21046250173998113555150755 31569375260997170332726133)
      ·
        refine ⟨2959628930718484718693075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31569375260997170332726133 2959628930718484718693075)
        ·
          refine ⟨4439443396077727078039613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2959628930718484718693075 4439443396077727078039613)
          ·
            refine ⟨1664791273529147654264855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4439443396077727078039613 1664791273529147654264855)
            ·
              refine ⟨2497186910293721481397283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664791273529147654264855 2497186910293721481397283)
              ·
                refine ⟨3745780365440582222095925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497186910293721481397283 3745780365440582222095925)
                ·
                  refine ⟨351166909260054583321493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3745780365440582222095925 351166909260054583321493)
                  ·
                    rfl

theorem cell21_1538764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_1538764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538764 prefixEnd_1538764 := by exact prefixLift 1538764
  have htrace : WordTrace (prefixWord ++ tailWord_1538764) baseStart_1538764 baseEnd_1538764 := by
    simpa [prefixWord, tailWord_1538764, baseEnd_1538764] using wordTrace_append hprefix tailTrace_1538764
  have hstable : (prefixWord ++ tailWord_1538764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538764).length < 2 ^ (prefixWord ++ tailWord_1538764).sum := by decide
  have hdescent : baseEnd_1538764 < baseStart_1538764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538775 : List Nat := [1, 1, 3, 2, 1, 4, 1, 8]
def baseStart_1538775 : Nat := 118140960795 + 1538775 * 2 ^ 59
def prefixEnd_1538775 : Nat := 4983230072969 + 3 ^ 40 * 1538775 * 2
def baseEnd_1538775 : Nat := 117056473203307002879379

theorem tailTrace_1538775 : CollatzResearch.WordTrace tailWord_1538775 prefixEnd_1538775 117056473203307002879379 := by
  unfold tailWord_1538775
  simp only [CollatzResearch.WordTrace]
  refine ⟨56123735000288451692385779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37415823333525634461590519 56123735000288451692385779)
  ·
    refine ⟨84185602500432677538578669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56123735000288451692385779 84185602500432677538578669)
    ·
      refine ⟨31569600937662254076967001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84185602500432677538578669 31569600937662254076967001)
      ·
        refine ⟨23677200703246690557725251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31569600937662254076967001 23677200703246690557725251)
        ·
          refine ⟨35515801054870035836587877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23677200703246690557725251 35515801054870035836587877)
          ·
            refine ⟨6659212697788131719360227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35515801054870035836587877 6659212697788131719360227)
            ·
              refine ⟨9988819046682197579040341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6659212697788131719360227 9988819046682197579040341)
              ·
                refine ⟨117056473203307002879379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9988819046682197579040341 117056473203307002879379)
                ·
                  rfl

theorem cell21_1538775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 8].length) (baseStart_1538775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538775 prefixEnd_1538775 := by exact prefixLift 1538775
  have htrace : WordTrace (prefixWord ++ tailWord_1538775) baseStart_1538775 baseEnd_1538775 := by
    simpa [prefixWord, tailWord_1538775, baseEnd_1538775] using wordTrace_append hprefix tailTrace_1538775
  have hstable : (prefixWord ++ tailWord_1538775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538775).length < 2 ^ (prefixWord ++ tailWord_1538775).sum := by decide
  have hdescent : baseEnd_1538775 < baseStart_1538775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538837 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 4]
def baseStart_1538837 : Nat := 118140960795 + 1538837 * 2 ^ 59
def prefixEnd_1538837 : Nat := 4983230072969 + 3 ^ 40 * 1538837 * 2
def baseEnd_1538837 : Nat := 351183568854622678604677

theorem tailTrace_1538837 : CollatzResearch.WordTrace tailWord_1538837 prefixEnd_1538837 351183568854622678604677 := by
  unfold tailWord_1538837
  simp only [CollatzResearch.WordTrace]
  refine ⟨56125996326063836281142765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37417330884042557520761843 56125996326063836281142765)
  ·
    refine ⟨21047248622273938605428537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56125996326063836281142765 21047248622273938605428537)
    ·
      refine ⟨15785436466705453954071403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21047248622273938605428537 15785436466705453954071403)
      ·
        refine ⟨23678154700058180931107105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15785436466705453954071403 23678154700058180931107105)
        ·
          refine ⟨17758616025043635698330329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23678154700058180931107105 17758616025043635698330329)
          ·
            refine ⟨13318962018782726773747747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17758616025043635698330329 13318962018782726773747747)
            ·
              refine ⟨19978443028174090160621621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13318962018782726773747747 19978443028174090160621621)
              ·
                refine ⟨1872979033891320952558277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19978443028174090160621621 1872979033891320952558277)
                ·
                  refine ⟨351183568854622678604677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1872979033891320952558277 351183568854622678604677)
                  ·
                    rfl

theorem cell21_1538837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_1538837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538837 prefixEnd_1538837 := by exact prefixLift 1538837
  have htrace : WordTrace (prefixWord ++ tailWord_1538837) baseStart_1538837 baseEnd_1538837 := by
    simpa [prefixWord, tailWord_1538837, baseEnd_1538837] using wordTrace_append hprefix tailTrace_1538837
  have hstable : (prefixWord ++ tailWord_1538837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538837).length < 2 ^ (prefixWord ++ tailWord_1538837).sum := by decide
  have hdescent : baseEnd_1538837 < baseStart_1538837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538916 : List Nat := [2, 3, 1, 1, 4, 1, 3, 3, 3]
def baseStart_1538916 : Nat := 118140960795 + 1538916 * 2 ^ 59
def prefixEnd_1538916 : Nat := 4983230072969 + 3 ^ 40 * 1538916 * 2
def baseEnd_1538916 : Nat := 351201597730936096787849

theorem tailTrace_1538916 : CollatzResearch.WordTrace tailWord_1538916 prefixEnd_1538916 351201597730936096787849 := by
  unfold tailWord_1538916
  simp only [CollatzResearch.WordTrace]
  refine ⟨28064438846388816386634301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37419251795185088515512401 28064438846388816386634301)
  ·
    refine ⟨10524164567395806144987863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28064438846388816386634301 10524164567395806144987863)
    ·
      refine ⟨15786246851093709217481795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10524164567395806144987863 15786246851093709217481795)
      ·
        refine ⟨23679370276640563826222693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15786246851093709217481795 23679370276640563826222693)
        ·
          refine ⟨4439881926870105717416755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23679370276640563826222693 4439881926870105717416755)
          ·
            refine ⟨6659822890305158576125133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4439881926870105717416755 6659822890305158576125133)
            ·
              refine ⟨2497433583864434466046925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6659822890305158576125133 2497433583864434466046925)
              ·
                refine ⟨936537593949162924767597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2497433583864434466046925 936537593949162924767597)
                ·
                  refine ⟨351201597730936096787849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936537593949162924767597 351201597730936096787849)
                  ·
                    rfl

theorem cell21_1538916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_1538916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538916 prefixEnd_1538916 := by exact prefixLift 1538916
  have htrace : WordTrace (prefixWord ++ tailWord_1538916) baseStart_1538916 baseEnd_1538916 := by
    simpa [prefixWord, tailWord_1538916, baseEnd_1538916] using wordTrace_append hprefix tailTrace_1538916
  have hstable : (prefixWord ++ tailWord_1538916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538916).length < 2 ^ (prefixWord ++ tailWord_1538916).sum := by decide
  have hdescent : baseEnd_1538916 < baseStart_1538916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538933 : List Nat := [1, 3, 4, 1, 1, 3, 3, 2, 3]
def baseStart_1538933 : Nat := 118140960795 + 1538933 * 2 ^ 59
def prefixEnd_1538933 : Nat := 4983230072969 + 3 ^ 40 * 1538933 * 2
def baseEnd_1538933 : Nat := 351205477362547845004481

theorem tailTrace_1538933 : CollatzResearch.WordTrace tailWord_1538933 prefixEnd_1538933 351205477362547845004481 := by
  unfold tailWord_1538933
  simp only [CollatzResearch.WordTrace]
  refine ⟨56129497733716044676637453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37419665155810696451091635 56129497733716044676637453)
  ·
    refine ⟨21048561650143516753739045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56129497733716044676637453 21048561650143516753739045)
    ·
      refine ⟨3946605309401909391326071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21048561650143516753739045 3946605309401909391326071)
      ·
        refine ⟨5919907964102864086989107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3946605309401909391326071 5919907964102864086989107)
        ·
          refine ⟨8879861946154296130483661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5919907964102864086989107 8879861946154296130483661)
          ·
            refine ⟨3329948229807861048931373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8879861946154296130483661 3329948229807861048931373)
            ·
              refine ⟨1248730586177947893349265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3329948229807861048931373 1248730586177947893349265)
              ·
                refine ⟨936547939633460920011949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1248730586177947893349265 936547939633460920011949)
                ·
                  refine ⟨351205477362547845004481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936547939633460920011949 351205477362547845004481)
                  ·
                    rfl

theorem cell21_1538933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_1538933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1538933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1538933 prefixEnd_1538933 := by exact prefixLift 1538933
  have htrace : WordTrace (prefixWord ++ tailWord_1538933) baseStart_1538933 baseEnd_1538933 := by
    simpa [prefixWord, tailWord_1538933, baseEnd_1538933] using wordTrace_append hprefix tailTrace_1538933
  have hstable : (prefixWord ++ tailWord_1538933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538933).length < 2 ^ (prefixWord ++ tailWord_1538933).sum := by decide
  have hdescent : baseEnd_1538933 < baseStart_1538933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539020 : List Nat := [2, 2, 1, 4, 1, 1, 5, 5]
def baseStart_1539020 : Nat := 118140960795 + 1539020 * 2 ^ 59
def prefixEnd_1539020 : Nat := 4983230072969 + 3 ^ 40 * 1539020 * 2
def baseEnd_1539020 : Nat := 117075110649285009018101

theorem tailTrace_1539020 : CollatzResearch.WordTrace tailWord_1539020 prefixEnd_1539020 117075110649285009018101 := by
  unfold tailWord_1539020
  simp only [CollatzResearch.WordTrace]
  refine ⟨28066335442200429267527257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37421780589600572356703009 28066335442200429267527257)
  ·
    refine ⟨21049751581650321950645443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28066335442200429267527257 21049751581650321950645443)
    ·
      refine ⟨31574627372475482925968165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21049751581650321950645443 31574627372475482925968165)
      ·
        refine ⟨5920242632339153048619031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31574627372475482925968165 5920242632339153048619031)
        ·
          refine ⟨8880363948508729572928547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5920242632339153048619031 8880363948508729572928547)
          ·
            refine ⟨13320545922763094359392821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8880363948508729572928547 13320545922763094359392821)
            ·
              refine ⟨1248801180259040096193077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13320545922763094359392821 1248801180259040096193077)
              ·
                refine ⟨117075110649285009018101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1248801180259040096193077 117075110649285009018101)
                ·
                  rfl

theorem cell21_1539020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_1539020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539020 prefixEnd_1539020 := by exact prefixLift 1539020
  have htrace : WordTrace (prefixWord ++ tailWord_1539020) baseStart_1539020 baseEnd_1539020 := by
    simpa [prefixWord, tailWord_1539020, baseEnd_1539020] using wordTrace_append hprefix tailTrace_1539020
  have hstable : (prefixWord ++ tailWord_1539020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539020).length < 2 ^ (prefixWord ++ tailWord_1539020).sum := by decide
  have hdescent : baseEnd_1539020 < baseStart_1539020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539079 : List Nat := [1, 1, 4, 3, 1, 1, 3, 7]
def baseStart_1539079 : Nat := 118140960795 + 1539079 * 2 ^ 59
def prefixEnd_1539079 : Nat := 4983230072969 + 3 ^ 40 * 1539079 * 2
def baseEnd_1539079 : Nat := 117079598850561345190283

theorem tailTrace_1539079 : CollatzResearch.WordTrace tailWord_1539079 prefixEnd_1539079 117079598850561345190283 := by
  unfold tailWord_1539079
  simp only [CollatzResearch.WordTrace]
  refine ⟨56134822791187111611452291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37423215194124741074301527 56134822791187111611452291)
  ·
    refine ⟨84202234186780667417178437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56134822791187111611452291 84202234186780667417178437)
    ·
      refine ⟨15787918910021375140720957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84202234186780667417178437 15787918910021375140720957)
      ·
        refine ⟨5920469591258015677770359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15787918910021375140720957 5920469591258015677770359)
        ·
          refine ⟨8880704386887023516655539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5920469591258015677770359 8880704386887023516655539)
          ·
            refine ⟨13321056580330535274983309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8880704386887023516655539 13321056580330535274983309)
            ·
              refine ⟨4995396217623950728118741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13321056580330535274983309 4995396217623950728118741)
              ·
                refine ⟨117079598850561345190283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4995396217623950728118741 117079598850561345190283)
                ·
                  rfl

theorem cell21_1539079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 7].length) (baseStart_1539079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539079 prefixEnd_1539079 := by exact prefixLift 1539079
  have htrace : WordTrace (prefixWord ++ tailWord_1539079) baseStart_1539079 baseEnd_1539079 := by
    simpa [prefixWord, tailWord_1539079, baseEnd_1539079] using wordTrace_append hprefix tailTrace_1539079
  have hstable : (prefixWord ++ tailWord_1539079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539079).length < 2 ^ (prefixWord ++ tailWord_1539079).sum := by decide
  have hdescent : baseEnd_1539079 < baseStart_1539079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539186 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1539186 : Nat := 118140960795 + 1539186 * 2 ^ 59
def prefixEnd_1539186 : Nat := 4983230072969 + 3 ^ 40 * 1539186 * 2
def baseEnd_1539186 : Nat := 351263215409475627287297

theorem tailTrace_1539186 : CollatzResearch.WordTrace tailWord_1539186 prefixEnd_1539186 351263215409475627287297 := by
  unfold tailWord_1539186
  simp only [CollatzResearch.WordTrace]
  refine ⟨14034681350449867221399353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37425816934532979257064941 14034681350449867221399353)
  ·
    refine ⟨10526011012837400416049515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14034681350449867221399353 10526011012837400416049515)
    ·
      refine ⟨15789016519256100624074273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10526011012837400416049515 15789016519256100624074273)
      ·
        refine ⟨11841762389442075468055705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15789016519256100624074273 11841762389442075468055705)
        ·
          refine ⟨8881321792081556601041779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11841762389442075468055705 8881321792081556601041779)
          ·
            refine ⟨13321982688122334901562669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8881321792081556601041779 13321982688122334901562669)
            ·
              refine ⟨4995743508045875588086001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13321982688122334901562669 4995743508045875588086001)
              ·
                refine ⟨3746807631034406691064501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4995743508045875588086001 3746807631034406691064501)
                ·
                  refine ⟨351263215409475627287297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3746807631034406691064501 351263215409475627287297)
                  ·
                    rfl

theorem cell21_1539186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1539186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539186 prefixEnd_1539186 := by exact prefixLift 1539186
  have htrace : WordTrace (prefixWord ++ tailWord_1539186) baseStart_1539186 baseEnd_1539186 := by
    simpa [prefixWord, tailWord_1539186, baseEnd_1539186] using wordTrace_append hprefix tailTrace_1539186
  have hstable : (prefixWord ++ tailWord_1539186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539186).length < 2 ^ (prefixWord ++ tailWord_1539186).sum := by decide
  have hdescent : baseEnd_1539186 < baseStart_1539186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539203 : List Nat := [1, 1, 1, 3, 3, 2, 4, 3, 3]
def baseStart_1539203 : Nat := 118140960795 + 1539203 * 2 ^ 59
def prefixEnd_1539203 : Nat := 4983230072969 + 3 ^ 40 * 1539203 * 2
def baseEnd_1539203 : Nat := 351267095041087375503929

theorem tailTrace_1539203 : CollatzResearch.WordTrace tailWord_1539203 prefixEnd_1539203 351267095041087375503929 := by
  unfold tailWord_1539203
  simp only [CollatzResearch.WordTrace]
  refine ⟨56139345442737880788966263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37426230295158587192644175 56139345442737880788966263)
  ·
    refine ⟨84209018164106821183449395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56139345442737880788966263 84209018164106821183449395)
    ·
      refine ⟨126313527246160231775174093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84209018164106821183449395 126313527246160231775174093)
      ·
        refine ⟨47367572717310086915690285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126313527246160231775174093 47367572717310086915690285)
        ·
          refine ⟨17762839768991282593383857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47367572717310086915690285 17762839768991282593383857)
          ·
            refine ⟨13322129826743461945037893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17762839768991282593383857 13322129826743461945037893)
            ·
              refine ⟨2497899342514399114694605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13322129826743461945037893 2497899342514399114694605)
              ·
                refine ⟨936712253442899668010477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2497899342514399114694605 936712253442899668010477)
                ·
                  refine ⟨351267095041087375503929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936712253442899668010477 351267095041087375503929)
                  ·
                    rfl

theorem cell21_1539203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 3].length) (baseStart_1539203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539203 prefixEnd_1539203 := by exact prefixLift 1539203
  have htrace : WordTrace (prefixWord ++ tailWord_1539203) baseStart_1539203 baseEnd_1539203 := by
    simpa [prefixWord, tailWord_1539203, baseEnd_1539203] using wordTrace_append hprefix tailTrace_1539203
  have hstable : (prefixWord ++ tailWord_1539203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539203).length < 2 ^ (prefixWord ++ tailWord_1539203).sum := by decide
  have hdescent : baseEnd_1539203 < baseStart_1539203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539330 : List Nat := [3, 4, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1539330 : Nat := 118140960795 + 1539330 * 2 ^ 59
def prefixEnd_1539330 : Nat := 4983230072969 + 3 ^ 40 * 1539330 * 2
def baseEnd_1539330 : Nat := 351296078171363376887003

theorem tailTrace_1539330 : CollatzResearch.WordTrace tailWord_1539330 prefixEnd_1539330 351296078171363376887003 := by
  unfold tailWord_1539330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14035994378319445369709861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37429318342185187652559629 14035994378319445369709861)
  ·
    refine ⟨2631748945934896006820599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14035994378319445369709861 2631748945934896006820599)
    ·
      refine ⟨3947623418902344010230899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2631748945934896006820599 3947623418902344010230899)
      ·
        refine ⟨5921435128353516015346349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3947623418902344010230899 5921435128353516015346349)
        ·
          refine ⟨2220538173132568505754881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5921435128353516015346349 2220538173132568505754881)
          ·
            refine ⟨1665403629849426379316161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2220538173132568505754881 1665403629849426379316161)
            ·
              refine ⟨1249052722387069784487121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665403629849426379316161 1249052722387069784487121)
              ·
                refine ⟨936789541790302338365341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249052722387069784487121 936789541790302338365341)
                ·
                  refine ⟨351296078171363376887003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936789541790302338365341 351296078171363376887003)
                  ·
                    rfl

theorem cell21_1539330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1539330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539330 prefixEnd_1539330 := by exact prefixLift 1539330
  have htrace : WordTrace (prefixWord ++ tailWord_1539330) baseStart_1539330 baseEnd_1539330 := by
    simpa [prefixWord, tailWord_1539330, baseEnd_1539330] using wordTrace_append hprefix tailTrace_1539330
  have hstable : (prefixWord ++ tailWord_1539330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539330).length < 2 ^ (prefixWord ++ tailWord_1539330).sum := by decide
  have hdescent : baseEnd_1539330 < baseStart_1539330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539358 : List Nat := [4, 3, 2, 1, 2, 1, 3, 5]
def baseStart_1539358 : Nat := 118140960795 + 1539358 * 2 ^ 59
def prefixEnd_1539358 : Nat := 4983230072969 + 3 ^ 40 * 1539358 * 2
def baseEnd_1539358 : Nat := 117100822717613850140093

theorem tailTrace_1539358 : CollatzResearch.WordTrace tailWord_1539358 prefixEnd_1539358 117100822717613850140093 := by
  unfold tailWord_1539358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018124844647042782607341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37429999171450894840572485 7018124844647042782607341)
  ·
    refine ⟨2631796816742641043477753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7018124844647042782607341 2631796816742641043477753)
    ·
      refine ⟨1973847612556980782608315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2631796816742641043477753 1973847612556980782608315)
      ·
        refine ⟨2960771418835471173912473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973847612556980782608315 2960771418835471173912473)
        ·
          refine ⟨2220578564126603380434355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2960771418835471173912473 2220578564126603380434355)
          ·
            refine ⟨3330867846189905070651533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220578564126603380434355 3330867846189905070651533)
            ·
              refine ⟨1249075442321214401494325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3330867846189905070651533 1249075442321214401494325)
              ·
                refine ⟨117100822717613850140093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1249075442321214401494325 117100822717613850140093)
                ·
                  rfl

theorem cell21_1539358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_1539358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539358 prefixEnd_1539358 := by exact prefixLift 1539358
  have htrace : WordTrace (prefixWord ++ tailWord_1539358) baseStart_1539358 baseEnd_1539358 := by
    simpa [prefixWord, tailWord_1539358, baseEnd_1539358] using wordTrace_append hprefix tailTrace_1539358
  have hstable : (prefixWord ++ tailWord_1539358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539358).length < 2 ^ (prefixWord ++ tailWord_1539358).sum := by decide
  have hdescent : baseEnd_1539358 < baseStart_1539358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539428 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_1539428 : Nat := 118140960795 + 1539428 * 2 ^ 59
def prefixEnd_1539428 : Nat := 4983230072969 + 3 ^ 40 * 1539428 * 2
def baseEnd_1539428 : Nat := 351318443106536984253469

theorem tailTrace_1539428 : CollatzResearch.WordTrace tailWord_1539428 prefixEnd_1539428 351318443106536984253469 := by
  unfold tailWord_1539428
  simp only [CollatzResearch.WordTrace]
  refine ⟨28073775933461372107953469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37431701244615162810604625 28073775933461372107953469)
  ·
    refine ⟨10527665975048014540482551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28073775933461372107953469 10527665975048014540482551)
    ·
      refine ⟨15791498962572021810723827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10527665975048014540482551 15791498962572021810723827)
      ·
        refine ⟨23687248443858032716085741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15791498962572021810723827 23687248443858032716085741)
        ·
          refine ⟨8882718166446762268532153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23687248443858032716085741 8882718166446762268532153)
          ·
            refine ⟨6662038624835071701399115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8882718166446762268532153 6662038624835071701399115)
            ·
              refine ⟨9993057937252607552098673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662038624835071701399115 9993057937252607552098673)
              ·
                refine ⟨7494793452939455664074005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9993057937252607552098673 7494793452939455664074005)
                ·
                  refine ⟨351318443106536984253469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7494793452939455664074005 351318443106536984253469)
                  ·
                    rfl

theorem cell21_1539428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_1539428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539428 prefixEnd_1539428 := by exact prefixLift 1539428
  have htrace : WordTrace (prefixWord ++ tailWord_1539428) baseStart_1539428 baseEnd_1539428 := by
    simpa [prefixWord, tailWord_1539428, baseEnd_1539428] using wordTrace_append hprefix tailTrace_1539428
  have hstable : (prefixWord ++ tailWord_1539428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539428).length < 2 ^ (prefixWord ++ tailWord_1539428).sum := by decide
  have hdescent : baseEnd_1539428 < baseStart_1539428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539459 : List Nat := [1, 1, 1, 3, 5, 2, 2, 6]
def baseStart_1539459 : Nat := 118140960795 + 1539459 * 2 ^ 59
def prefixEnd_1539459 : Nat := 4983230072969 + 3 ^ 40 * 1539459 * 2
def baseEnd_1539459 : Nat := 117108505909629273078913

theorem tailTrace_1539459 : CollatzResearch.WordTrace tailWord_1539459 prefixEnd_1539459 117108505909629273078913 := by
  unfold tailWord_1539459
  simp only [CollatzResearch.WordTrace]
  refine ⟨56148682529810436510285431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37432455019873624340190287 56148682529810436510285431)
  ·
    refine ⟨84223023794715654765428147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56148682529810436510285431 84223023794715654765428147)
    ·
      refine ⟨126334535692073482148142221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84223023794715654765428147 126334535692073482148142221)
      ·
        refine ⟨47375450884527555805553333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126334535692073482148142221 47375450884527555805553333)
        ·
          refine ⟨4441448520424458356770625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47375450884527555805553333 4441448520424458356770625)
          ·
            refine ⟨3331086390318343767577969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4441448520424458356770625 3331086390318343767577969)
            ·
              refine ⟨2498314792738757825683477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3331086390318343767577969 2498314792738757825683477)
              ·
                refine ⟨117108505909629273078913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2498314792738757825683477 117108505909629273078913)
                ·
                  rfl

theorem cell21_1539459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 6].length) (baseStart_1539459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539459 prefixEnd_1539459 := by exact prefixLift 1539459
  have htrace : WordTrace (prefixWord ++ tailWord_1539459) baseStart_1539459 baseEnd_1539459 := by
    simpa [prefixWord, tailWord_1539459, baseEnd_1539459] using wordTrace_append hprefix tailTrace_1539459
  have hstable : (prefixWord ++ tailWord_1539459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539459).length < 2 ^ (prefixWord ++ tailWord_1539459).sum := by decide
  have hdescent : baseEnd_1539459 < baseStart_1539459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539566 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_1539566 : Nat := 118140960795 + 1539566 * 2 ^ 59
def prefixEnd_1539566 : Nat := 4983230072969 + 3 ^ 40 * 1539566 * 2
def baseEnd_1539566 : Nat := 351349936586679410953187

theorem tailTrace_1539566 : CollatzResearch.WordTrace tailWord_1539566 prefixEnd_1539566 351349936586679410953187 := by
  unfold tailWord_1539566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7019073142552849223053819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37435056760281862522953701 7019073142552849223053819)
  ·
    refine ⟨10528609713829273834580729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7019073142552849223053819 10528609713829273834580729)
    ·
      refine ⟨7896457285371955375935547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10528609713829273834580729 7896457285371955375935547)
      ·
        refine ⟨11844685928057933063903321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7896457285371955375935547 11844685928057933063903321)
        ·
          refine ⟨8883514446043449797927491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11844685928057933063903321 8883514446043449797927491)
          ·
            refine ⟨13325271669065174696891237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8883514446043449797927491 13325271669065174696891237)
            ·
              refine ⟨2498488437949720255667107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13325271669065174696891237 2498488437949720255667107)
              ·
                refine ⟨3747732656924580383500661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498488437949720255667107 3747732656924580383500661)
                ·
                  refine ⟨351349936586679410953187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3747732656924580383500661 351349936586679410953187)
                  ·
                    rfl

theorem cell21_1539566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_1539566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539566 prefixEnd_1539566 := by exact prefixLift 1539566
  have htrace : WordTrace (prefixWord ++ tailWord_1539566) baseStart_1539566 baseEnd_1539566 := by
    simpa [prefixWord, tailWord_1539566, baseEnd_1539566] using wordTrace_append hprefix tailTrace_1539566
  have hstable : (prefixWord ++ tailWord_1539566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539566).length < 2 ^ (prefixWord ++ tailWord_1539566).sum := by decide
  have hdescent : baseEnd_1539566 < baseStart_1539566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539580 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_1539580 : Nat := 118140960795 + 1539580 * 2 ^ 59
def prefixEnd_1539580 : Nat := 4983230072969 + 3 ^ 40 * 1539580 * 2
def baseEnd_1539580 : Nat := 351353131577418497719825

theorem tailTrace_1539580 : CollatzResearch.WordTrace tailWord_1539580 prefixEnd_1539580 351353131577418497719825 := by
  unfold tailWord_1539580
  simp only [CollatzResearch.WordTrace]
  refine ⟨28076547881186037087720097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37435397174914716116960129 28076547881186037087720097)
  ·
    refine ⟨21057410910889527815790073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28076547881186037087720097 21057410910889527815790073)
    ·
      refine ⟨15793058183167145861842555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21057410910889527815790073 15793058183167145861842555)
      ·
        refine ⟨23689587274750718792763833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15793058183167145861842555 23689587274750718792763833)
        ·
          refine ⟨17767190456063039094572875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23689587274750718792763833 17767190456063039094572875)
          ·
            refine ⟨26650785684094558641859313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17767190456063039094572875 26650785684094558641859313)
            ·
              refine ⟨19988089263070918981394485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26650785684094558641859313 19988089263070918981394485)
              ·
                refine ⟨1873883368412898654505733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19988089263070918981394485 1873883368412898654505733)
                ·
                  refine ⟨351353131577418497719825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1873883368412898654505733 351353131577418497719825)
                  ·
                    rfl

theorem cell21_1539580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_1539580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539580 prefixEnd_1539580 := by exact prefixLift 1539580
  have htrace : WordTrace (prefixWord ++ tailWord_1539580) baseStart_1539580 baseEnd_1539580 := by
    simpa [prefixWord, tailWord_1539580, baseEnd_1539580] using wordTrace_append hprefix tailTrace_1539580
  have hstable : (prefixWord ++ tailWord_1539580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539580).length < 2 ^ (prefixWord ++ tailWord_1539580).sum := by decide
  have hdescent : baseEnd_1539580 < baseStart_1539580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539676 : List Nat := [2, 2, 4, 1, 2, 1, 4, 2, 3]
def baseStart_1539676 : Nat := 118140960795 + 1539676 * 2 ^ 59
def prefixEnd_1539676 : Nat := 4983230072969 + 3 ^ 40 * 1539676 * 2
def baseEnd_1539676 : Nat := 351375040085343664119629

theorem tailTrace_1539676 : CollatzResearch.WordTrace tailWord_1539676 prefixEnd_1539676 351375040085343664119629 := by
  unfold tailWord_1539676
  simp only [CollatzResearch.WordTrace]
  refine ⟨28078298585012141285467441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37437731446682855047289921 28078298585012141285467441)
  ·
    refine ⟨21058723938759105964100581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28078298585012141285467441 21058723938759105964100581)
    ·
      refine ⟨3948510738517332368268859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21058723938759105964100581 3948510738517332368268859)
      ·
        refine ⟨5922766107775998552403289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3948510738517332368268859 5922766107775998552403289)
        ·
          refine ⟨4442074580831998914302467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5922766107775998552403289 4442074580831998914302467)
          ·
            refine ⟨6663111871247998371453701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4442074580831998914302467 6663111871247998371453701)
            ·
              refine ⟨1249333475858999694647569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6663111871247998371453701 1249333475858999694647569)
              ·
                refine ⟨937000106894249770985677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249333475858999694647569 937000106894249770985677)
                ·
                  refine ⟨351375040085343664119629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937000106894249770985677 351375040085343664119629)
                  ·
                    rfl

theorem cell21_1539676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_1539676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539676 prefixEnd_1539676 := by exact prefixLift 1539676
  have htrace : WordTrace (prefixWord ++ tailWord_1539676) baseStart_1539676 baseEnd_1539676 := by
    simpa [prefixWord, tailWord_1539676, baseEnd_1539676] using wordTrace_append hprefix tailTrace_1539676
  have hstable : (prefixWord ++ tailWord_1539676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539676).length < 2 ^ (prefixWord ++ tailWord_1539676).sum := by decide
  have hdescent : baseEnd_1539676 < baseStart_1539676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539715 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 6]
def baseStart_1539715 : Nat := 118140960795 + 1539715 * 2 ^ 59
def prefixEnd_1539715 : Nat := 4983230072969 + 3 ^ 40 * 1539715 * 2
def baseEnd_1539715 : Nat := 351383940416688262969549

theorem tailTrace_1539715 : CollatzResearch.WordTrace tailWord_1539715 prefixEnd_1539715 351383940416688262969549 := by
  unfold tailWord_1539715
  simp only [CollatzResearch.WordTrace]
  refine ⟨56158019616882992231604599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37438679744588661487736399 56158019616882992231604599)
  ·
    refine ⟨84237029425324488347406899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56158019616882992231604599 84237029425324488347406899)
    ·
      refine ⟨126355544137986732521110349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84237029425324488347406899 126355544137986732521110349)
      ·
        refine ⟨47383329051745024695416381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126355544137986732521110349 47383329051745024695416381)
        ·
          refine ⟨17768748394404384260781143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47383329051745024695416381 17768748394404384260781143)
          ·
            refine ⟨26653122591606576391171715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17768748394404384260781143 26653122591606576391171715)
            ·
              refine ⟨39979683887409864586757573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26653122591606576391171715 39979683887409864586757573)
              ·
                refine ⟨7496190728889349610017045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39979683887409864586757573 7496190728889349610017045)
                ·
                  refine ⟨351383940416688262969549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7496190728889349610017045 351383940416688262969549)
                  ·
                    rfl

theorem cell21_1539715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_1539715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539715 prefixEnd_1539715 := by exact prefixLift 1539715
  have htrace : WordTrace (prefixWord ++ tailWord_1539715) baseStart_1539715 baseEnd_1539715 := by
    simpa [prefixWord, tailWord_1539715, baseEnd_1539715] using wordTrace_append hprefix tailTrace_1539715
  have hstable : (prefixWord ++ tailWord_1539715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539715).length < 2 ^ (prefixWord ++ tailWord_1539715).sum := by decide
  have hdescent : baseEnd_1539715 < baseStart_1539715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539794 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_1539794 : Nat := 118140960795 + 1539794 * 2 ^ 59
def prefixEnd_1539794 : Nat := 4983230072969 + 3 ^ 40 * 1539794 * 2
def baseEnd_1539794 : Nat := 351401969293001681152721

theorem tailTrace_1539794 : CollatzResearch.WordTrace tailWord_1539794 prefixEnd_1539794 351401969293001681152721 := by
  unfold tailWord_1539794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14040225245899197180932609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37440600655731192482486957 14040225245899197180932609)
  ·
    refine ⟨10530168934424397885699457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14040225245899197180932609 10530168934424397885699457)
    ·
      refine ⟨7897626700818298414274593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10530168934424397885699457 7897626700818298414274593)
      ·
        refine ⟨5923220025613723810705945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7897626700818298414274593 5923220025613723810705945)
        ·
          refine ⟨4442415019210292858029459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5923220025613723810705945 4442415019210292858029459)
          ·
            refine ⟨6663622528815439287044189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4442415019210292858029459 6663622528815439287044189)
            ·
              refine ⟨2498858448305789732641571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6663622528815439287044189 2498858448305789732641571)
              ·
                refine ⟨3748287672458684598962357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498858448305789732641571 3748287672458684598962357)
                ·
                  refine ⟨351401969293001681152721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3748287672458684598962357 351401969293001681152721)
                  ·
                    rfl

theorem cell21_1539794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_1539794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539794 prefixEnd_1539794 := by exact prefixLift 1539794
  have htrace : WordTrace (prefixWord ++ tailWord_1539794) baseStart_1539794 baseEnd_1539794 := by
    simpa [prefixWord, tailWord_1539794, baseEnd_1539794] using wordTrace_append hprefix tailTrace_1539794
  have hstable : (prefixWord ++ tailWord_1539794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539794).length < 2 ^ (prefixWord ++ tailWord_1539794).sum := by decide
  have hdescent : baseEnd_1539794 < baseStart_1539794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539822 : List Nat := [4, 1, 2, 1, 1, 2, 1, 9]
def baseStart_1539822 : Nat := 118140960795 + 1539822 * 2 ^ 59
def prefixEnd_1539822 : Nat := 4983230072969 + 3 ^ 40 * 1539822 * 2
def baseEnd_1539822 : Nat := 117136119758159951561999

theorem tailTrace_1539822 : CollatzResearch.WordTrace tailWord_1539822 prefixEnd_1539822 117136119758159951561999 := by
  unfold tailWord_1539822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7020240278436918688218715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37441281484996899670499813 7020240278436918688218715)
  ·
    refine ⟨10530360417655378032328073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7020240278436918688218715 10530360417655378032328073)
    ·
      refine ⟨7897770313241533524246055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10530360417655378032328073 7897770313241533524246055)
      ·
        refine ⟨11846655469862300286369083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7897770313241533524246055 11846655469862300286369083)
        ·
          refine ⟨17769983204793450429553625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11846655469862300286369083 17769983204793450429553625)
          ·
            refine ⟨13327487403595087822165219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17769983204793450429553625 13327487403595087822165219)
            ·
              refine ⟨19991231105392631733247829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13327487403595087822165219 19991231105392631733247829)
              ·
                refine ⟨117136119758159951561999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19991231105392631733247829 117136119758159951561999)
                ·
                  rfl

theorem cell21_1539822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_1539822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539822 prefixEnd_1539822 := by exact prefixLift 1539822
  have htrace : WordTrace (prefixWord ++ tailWord_1539822) baseStart_1539822 baseEnd_1539822 := by
    simpa [prefixWord, tailWord_1539822, baseEnd_1539822] using wordTrace_append hprefix tailTrace_1539822
  have hstable : (prefixWord ++ tailWord_1539822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539822).length < 2 ^ (prefixWord ++ tailWord_1539822).sum := by decide
  have hdescent : baseEnd_1539822 < baseStart_1539822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539898 : List Nat := [3, 1, 1, 1, 5, 2, 8]
def baseStart_1539898 : Nat := 118140960795 + 1539898 * 2 ^ 59
def prefixEnd_1539898 : Nat := 4983230072969 + 3 ^ 40 * 1539898 * 2
def baseEnd_1539898 : Nat := 39047300389991179046575

theorem tailTrace_1539898 : CollatzResearch.WordTrace tailWord_1539898 prefixEnd_1539898 39047300389991179046575 := by
  unfold tailWord_1539898
  simp only [CollatzResearch.WordTrace]
  refine ⟨14041173543805003621379087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37443129450146676323677565 14041173543805003621379087)
  ·
    refine ⟨21061760315707505432068631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14041173543805003621379087 21061760315707505432068631)
    ·
      refine ⟨31592640473561258148102947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21061760315707505432068631 31592640473561258148102947)
      ·
        refine ⟨47388960710341887222154421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31592640473561258148102947 47388960710341887222154421)
        ·
          refine ⟨4442715066594551927076977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47388960710341887222154421 4442715066594551927076977)
          ·
            refine ⟨3332036299945913945307733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4442715066594551927076977 3332036299945913945307733)
            ·
              refine ⟨39047300389991179046575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3332036299945913945307733 39047300389991179046575)
              ·
                rfl

theorem cell21_1539898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 8].length) (baseStart_1539898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539898 prefixEnd_1539898 := by exact prefixLift 1539898
  have htrace : WordTrace (prefixWord ++ tailWord_1539898) baseStart_1539898 baseEnd_1539898 := by
    simpa [prefixWord, tailWord_1539898, baseEnd_1539898] using wordTrace_append hprefix tailTrace_1539898
  have hstable : (prefixWord ++ tailWord_1539898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539898).length < 2 ^ (prefixWord ++ tailWord_1539898).sum := by decide
  have hdescent : baseEnd_1539898 < baseStart_1539898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539901 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 4]
def baseStart_1539901 : Nat := 118140960795 + 1539901 * 2 ^ 59
def prefixEnd_1539901 : Nat := 4983230072969 + 3 ^ 40 * 1539901 * 2
def baseEnd_1539901 : Nat := 351426388150793272869169

theorem tailTrace_1539901 : CollatzResearch.WordTrace tailWord_1539901 prefixEnd_1539901 351426388150793272869169 := by
  unfold tailWord_1539901
  simp only [CollatzResearch.WordTrace]
  refine ⟨56164803594209145997875557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37443202396139430665250371 56164803594209145997875557)
  ·
    refine ⟨10530900673914214874601667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56164803594209145997875557 10530900673914214874601667)
    ·
      refine ⟨15796351010871322311902501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10530900673914214874601667 15796351010871322311902501)
      ·
        refine ⟨2961815814538372933481719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15796351010871322311902501 2961815814538372933481719)
        ·
          refine ⟨4442723721807559400222579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2961815814538372933481719 4442723721807559400222579)
          ·
            refine ⟨6664085582711339100333869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4442723721807559400222579 6664085582711339100333869)
            ·
              refine ⟨2499032093516752162625201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6664085582711339100333869 2499032093516752162625201)
              ·
                refine ⟨1874274070137564121968901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499032093516752162625201 1874274070137564121968901)
                ·
                  refine ⟨351426388150793272869169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1874274070137564121968901 351426388150793272869169)
                  ·
                    rfl

theorem cell21_1539901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_1539901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539901 prefixEnd_1539901 := by exact prefixLift 1539901
  have htrace : WordTrace (prefixWord ++ tailWord_1539901) baseStart_1539901 baseEnd_1539901 := by
    simpa [prefixWord, tailWord_1539901, baseEnd_1539901] using wordTrace_append hprefix tailTrace_1539901
  have hstable : (prefixWord ++ tailWord_1539901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539901).length < 2 ^ (prefixWord ++ tailWord_1539901).sum := by decide
  have hdescent : baseEnd_1539901 < baseStart_1539901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539943 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 8]
def baseStart_1539943 : Nat := 118140960795 + 1539943 * 2 ^ 59
def prefixEnd_1539943 : Nat := 4983230072969 + 3 ^ 40 * 1539943 * 2
def baseEnd_1539943 : Nat := 351435973123010533169083

theorem tailTrace_1539943 : CollatzResearch.WordTrace tailWord_1539943 prefixEnd_1539943 351435973123010533169083 := by
  unfold tailWord_1539943
  simp only [CollatzResearch.WordTrace]
  refine ⟨56166335460056987170904483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37444223640037991447269655 56166335460056987170904483)
  ·
    refine ⟨84249503190085480756356725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56166335460056987170904483 84249503190085480756356725)
    ·
      refine ⟨7898390924070513820908443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84249503190085480756356725 7898390924070513820908443)
      ·
        refine ⟨11847586386105770731362665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7898390924070513820908443 11847586386105770731362665)
        ·
          refine ⟨8885689789579328048521999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11847586386105770731362665 8885689789579328048521999)
          ·
            refine ⟨13328534684368992072782999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8885689789579328048521999 13328534684368992072782999)
            ·
              refine ⟨19992802026553488109174499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13328534684368992072782999 19992802026553488109174499)
              ·
                refine ⟨29989203039830232163761749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19992802026553488109174499 29989203039830232163761749)
                ·
                  refine ⟨351435973123010533169083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29989203039830232163761749 351435973123010533169083)
                  ·
                    rfl

theorem cell21_1539943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_1539943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1539943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1539943 prefixEnd_1539943 := by exact prefixLift 1539943
  have htrace : WordTrace (prefixWord ++ tailWord_1539943) baseStart_1539943 baseEnd_1539943 := by
    simpa [prefixWord, tailWord_1539943, baseEnd_1539943] using wordTrace_append hprefix tailTrace_1539943
  have hstable : (prefixWord ++ tailWord_1539943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539943).length < 2 ^ (prefixWord ++ tailWord_1539943).sum := by decide
  have hdescent : baseEnd_1539943 < baseStart_1539943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540008 : List Nat := [2, 1, 6, 2, 2, 8]
def baseStart_1540008 : Nat := 118140960795 + 1540008 * 2 ^ 59
def prefixEnd_1540008 : Nat := 4983230072969 + 3 ^ 40 * 1540008 * 2
def baseEnd_1540008 : Nat := 13016696555873513503171

theorem tailTrace_1540008 : CollatzResearch.WordTrace tailWord_1540008 prefixEnd_1540008 13016696555873513503171 := by
  unfold tailWord_1540008
  simp only [CollatzResearch.WordTrace]
  refine ⟨28084353102410751636010339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37445804136547668848013785 28084353102410751636010339)
  ·
    refine ⟨42126529653616127454015509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28084353102410751636010339 42126529653616127454015509)
    ·
      refine ⟨1974681077513255974406977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42126529653616127454015509 1974681077513255974406977)
      ·
        refine ⟨1481010808134941980805233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1974681077513255974406977 1481010808134941980805233)
        ·
          refine ⟨1110758106101206485603925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1481010808134941980805233 1110758106101206485603925)
          ·
            refine ⟨13016696555873513503171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1110758106101206485603925 13016696555873513503171)
            ·
              rfl

theorem cell21_1540008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 8].length) (baseStart_1540008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540008 prefixEnd_1540008 := by exact prefixLift 1540008
  have htrace : WordTrace (prefixWord ++ tailWord_1540008) baseStart_1540008 baseEnd_1540008 := by
    simpa [prefixWord, tailWord_1540008, baseEnd_1540008] using wordTrace_append hprefix tailTrace_1540008
  have hstable : (prefixWord ++ tailWord_1540008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540008).length < 2 ^ (prefixWord ++ tailWord_1540008).sum := by decide
  have hdescent : baseEnd_1540008 < baseStart_1540008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540095 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 4]
def baseStart_1540095 : Nat := 118140960795 + 1540095 * 2 ^ 59
def prefixEnd_1540095 : Nat := 4983230072969 + 3 ^ 40 * 1540095 * 2
def baseEnd_1540095 : Nat := 351470661593892046635439

theorem tailTrace_1540095 : CollatzResearch.WordTrace tailWord_1540095 prefixEnd_1540095 351470661593892046635439 := by
  unfold tailWord_1540095
  simp only [CollatzResearch.WordTrace]
  refine ⟨56171879355506317130437739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37447919570337544753625159 56171879355506317130437739)
  ·
    refine ⟨84257819033259475695656609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56171879355506317130437739 84257819033259475695656609)
    ·
      refine ⟨63193364274944606771742457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84257819033259475695656609 63193364274944606771742457)
      ·
        refine ⟨47395023206208455078806843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63193364274944606771742457 47395023206208455078806843)
        ·
          refine ⟨71092534809312682618210265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47395023206208455078806843 71092534809312682618210265)
          ·
            refine ⟨53319401106984511963657699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71092534809312682618210265 53319401106984511963657699)
            ·
              refine ⟨79979101660476767945486549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53319401106984511963657699 79979101660476767945486549)
              ·
                refine ⟨1874510195167424248722341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79979101660476767945486549 1874510195167424248722341)
                ·
                  refine ⟨351470661593892046635439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1874510195167424248722341 351470661593892046635439)
                  ·
                    rfl

theorem cell21_1540095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 4].length) (baseStart_1540095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540095 prefixEnd_1540095 := by exact prefixLift 1540095
  have htrace : WordTrace (prefixWord ++ tailWord_1540095) baseStart_1540095 baseEnd_1540095 := by
    simpa [prefixWord, tailWord_1540095, baseEnd_1540095] using wordTrace_append hprefix tailTrace_1540095
  have hstable : (prefixWord ++ tailWord_1540095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540095).length < 2 ^ (prefixWord ++ tailWord_1540095).sum := by decide
  have hdescent : baseEnd_1540095 < baseStart_1540095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540132 : List Nat := [2, 3, 1, 4, 2, 1, 3, 2, 3]
def baseStart_1540132 : Nat := 118140960795 + 1540132 * 2 ^ 59
def prefixEnd_1540132 : Nat := 4983230072969 + 3 ^ 40 * 1540132 * 2
def baseEnd_1540132 : Nat := 351479105497988204518697

theorem tailTrace_1540132 : CollatzResearch.WordTrace tailWord_1540132 prefixEnd_1540132 351479105497988204518697 := by
  unfold tailWord_1540132
  simp only [CollatzResearch.WordTrace]
  refine ⟨28086614428186136224767325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37448819237581514966356433 28086614428186136224767325)
  ·
    refine ⟨10532480410569801084287747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28086614428186136224767325 10532480410569801084287747)
    ·
      refine ⟨15798720615854701626431621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10532480410569801084287747 15798720615854701626431621)
      ·
        refine ⟨2962260115472756554955929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15798720615854701626431621 2962260115472756554955929)
        ·
          refine ⟨2221695086604567416216947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2962260115472756554955929 2221695086604567416216947)
          ·
            refine ⟨3332542629906851124325421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221695086604567416216947 3332542629906851124325421)
            ·
              refine ⟨1249703486215069171622033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3332542629906851124325421 1249703486215069171622033)
              ·
                refine ⟨937277614661301878716525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249703486215069171622033 937277614661301878716525)
                ·
                  refine ⟨351479105497988204518697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937277614661301878716525 351479105497988204518697)
                  ·
                    rfl

theorem cell21_1540132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_1540132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540132 prefixEnd_1540132 := by exact prefixLift 1540132
  have htrace : WordTrace (prefixWord ++ tailWord_1540132) baseStart_1540132 baseEnd_1540132 := by
    simpa [prefixWord, tailWord_1540132, baseEnd_1540132] using wordTrace_append hprefix tailTrace_1540132
  have hstable : (prefixWord ++ tailWord_1540132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540132).length < 2 ^ (prefixWord ++ tailWord_1540132).sum := by decide
  have hdescent : baseEnd_1540132 < baseStart_1540132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540140 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_1540140 : Nat := 118140960795 + 1540140 * 2 ^ 59
def prefixEnd_1540140 : Nat := 4983230072969 + 3 ^ 40 * 1540140 * 2
def baseEnd_1540140 : Nat := 351480931206981968385347

theorem tailTrace_1540140 : CollatzResearch.WordTrace tailWord_1540140 prefixEnd_1540140 351480931206981968385347 := by
  unfold tailWord_1540140
  simp only [CollatzResearch.WordTrace]
  refine ⟨28086760320171644907912937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37449013760228859877217249 28086760320171644907912937)
  ·
    refine ⟨21065070240128733680934703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28086760320171644907912937 21065070240128733680934703)
    ·
      refine ⟨31597605360193100521402055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21065070240128733680934703 31597605360193100521402055)
      ·
        refine ⟨47396408040289650782103083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31597605360193100521402055 47396408040289650782103083)
        ·
          refine ⟨71094612060434476173154625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47396408040289650782103083 71094612060434476173154625)
          ·
            refine ⟨53320959045325857129865969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71094612060434476173154625 53320959045325857129865969)
            ·
              refine ⟨39990719283994392847399477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53320959045325857129865969 39990719283994392847399477)
              ·
                refine ⟨3749129932874474329443701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39990719283994392847399477 3749129932874474329443701)
                ·
                  refine ⟨351480931206981968385347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3749129932874474329443701 351480931206981968385347)
                  ·
                    rfl

theorem cell21_1540140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_1540140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540140 prefixEnd_1540140 := by exact prefixLift 1540140
  have htrace : WordTrace (prefixWord ++ tailWord_1540140) baseStart_1540140 baseEnd_1540140 := by
    simpa [prefixWord, tailWord_1540140, baseEnd_1540140] using wordTrace_append hprefix tailTrace_1540140
  have hstable : (prefixWord ++ tailWord_1540140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540140).length < 2 ^ (prefixWord ++ tailWord_1540140).sum := by decide
  have hdescent : baseEnd_1540140 < baseStart_1540140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540188 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_1540188 : Nat := 118140960795 + 1540188 * 2 ^ 59
def prefixEnd_1540188 : Nat := 4983230072969 + 3 ^ 40 * 1540188 * 2
def baseEnd_1540188 : Nat := 351491885460944551585249

theorem tailTrace_1540188 : CollatzResearch.WordTrace tailWord_1540188 prefixEnd_1540188 351491885460944551585249 := by
  unfold tailWord_1540188
  simp only [CollatzResearch.WordTrace]
  refine ⟨28087635672084697006786609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37450180896112929342382145 28087635672084697006786609)
  ·
    refine ⟨21065726754063522755089957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28087635672084697006786609 21065726754063522755089957)
    ·
      refine ⟨3949823766386910516579367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21065726754063522755089957 3949823766386910516579367)
      ·
        refine ⟨5924735649580365774869051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3949823766386910516579367 5924735649580365774869051)
        ·
          refine ⟨8887103474370548662303577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5924735649580365774869051 8887103474370548662303577)
          ·
            refine ⟨6665327605777911496727683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8887103474370548662303577 6665327605777911496727683)
            ·
              refine ⟨9997991408666867245091525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6665327605777911496727683 9997991408666867245091525)
              ·
                refine ⟨1874623389125037608454661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9997991408666867245091525 1874623389125037608454661)
                ·
                  refine ⟨351491885460944551585249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1874623389125037608454661 351491885460944551585249)
                  ·
                    rfl

theorem cell21_1540188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_1540188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540188 prefixEnd_1540188 := by exact prefixLift 1540188
  have htrace : WordTrace (prefixWord ++ tailWord_1540188) baseStart_1540188 baseEnd_1540188 := by
    simpa [prefixWord, tailWord_1540188, baseEnd_1540188] using wordTrace_append hprefix tailTrace_1540188
  have hstable : (prefixWord ++ tailWord_1540188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540188).length < 2 ^ (prefixWord ++ tailWord_1540188).sum := by decide
  have hdescent : baseEnd_1540188 < baseStart_1540188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540250 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_1540250 : Nat := 118140960795 + 1540250 * 2 ^ 59
def prefixEnd_1540250 : Nat := 4983230072969 + 3 ^ 40 * 1540250 * 2
def baseEnd_1540250 : Nat := 351506034705646221551789

theorem tailTrace_1540250 : CollatzResearch.WordTrace tailWord_1540250 prefixEnd_1540250 351506034705646221551789 := by
  unfold tailWord_1540250
  simp only [CollatzResearch.WordTrace]
  refine ⟨14044383167486194650582551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37451688446629852401553469 14044383167486194650582551)
  ·
    refine ⟨21066574751229291975873827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14044383167486194650582551 21066574751229291975873827)
    ·
      refine ⟨31599862126843937963810741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21066574751229291975873827 31599862126843937963810741)
      ·
        refine ⟨2962487074391619184107257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31599862126843937963810741 2962487074391619184107257)
        ·
          refine ⟨2221865305793714388080443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2962487074391619184107257 2221865305793714388080443)
          ·
            refine ⟨3332797958690571582120665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221865305793714388080443 3332797958690571582120665)
            ·
              refine ⟨2499598469017928686590499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3332797958690571582120665 2499598469017928686590499)
              ·
                refine ⟨3749397703526893029885749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499598469017928686590499 3749397703526893029885749)
                ·
                  refine ⟨351506034705646221551789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3749397703526893029885749 351506034705646221551789)
                  ·
                    rfl

theorem cell21_1540250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_1540250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540250 prefixEnd_1540250 := by exact prefixLift 1540250
  have htrace : WordTrace (prefixWord ++ tailWord_1540250) baseStart_1540250 baseEnd_1540250 := by
    simpa [prefixWord, tailWord_1540250, baseEnd_1540250] using wordTrace_append hprefix tailTrace_1540250
  have hstable : (prefixWord ++ tailWord_1540250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540250).length < 2 ^ (prefixWord ++ tailWord_1540250).sum := by decide
  have hdescent : baseEnd_1540250 < baseStart_1540250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540261 : List Nat := [1, 3, 1, 2, 1, 3, 2, 8]
def baseStart_1540261 : Nat := 118140960795 + 1540261 * 2 ^ 59
def prefixEnd_1540261 : Nat := 4983230072969 + 3 ^ 40 * 1540261 * 2
def baseEnd_1540261 : Nat := 117169515018504215622811

theorem tailTrace_1540261 : CollatzResearch.WordTrace tailWord_1540261 prefixEnd_1540261 117169515018504215622811 := by
  unfold tailWord_1540261
  simp only [CollatzResearch.WordTrace]
  refine ⟨56177933872904927480980637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37451955915269951653987091 56177933872904927480980637)
  ·
    refine ⟨21066725202339347805367739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56177933872904927480980637 21066725202339347805367739)
    ·
      refine ⟨31600087803509021708051609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21066725202339347805367739 31600087803509021708051609)
      ·
        refine ⟨23700065852631766281038707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31600087803509021708051609 23700065852631766281038707)
        ·
          refine ⟨35550098778947649421558061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23700065852631766281038707 35550098778947649421558061)
          ·
            refine ⟨13331287042105368533084273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35550098778947649421558061 13331287042105368533084273)
            ·
              refine ⟨9998465281579026399813205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13331287042105368533084273 9998465281579026399813205)
              ·
                refine ⟨117169515018504215622811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9998465281579026399813205 117169515018504215622811)
                ·
                  rfl

theorem cell21_1540261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 8].length) (baseStart_1540261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540261 prefixEnd_1540261 := by exact prefixLift 1540261
  have htrace : WordTrace (prefixWord ++ tailWord_1540261) baseStart_1540261 baseEnd_1540261 := by
    simpa [prefixWord, tailWord_1540261, baseEnd_1540261] using wordTrace_append hprefix tailTrace_1540261
  have hstable : (prefixWord ++ tailWord_1540261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540261).length < 2 ^ (prefixWord ++ tailWord_1540261).sum := by decide
  have hdescent : baseEnd_1540261 < baseStart_1540261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540270 : List Nat := [4, 1, 4, 2, 2, 1, 2, 5]
def baseStart_1540270 : Nat := 118140960795 + 1540270 * 2 ^ 59
def prefixEnd_1540270 : Nat := 4983230072969 + 3 ^ 40 * 1540270 * 2
def baseEnd_1540270 : Nat := 117170199659376877072805

theorem tailTrace_1540270 : CollatzResearch.WordTrace tailWord_1540270 prefixEnd_1540270 117170199659376877072805 := by
  unfold tailWord_1540270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022282766234040252257283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37452174753248214678705509 7022282766234040252257283)
  ·
    refine ⟨10533424149351060378385925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7022282766234040252257283 10533424149351060378385925)
    ·
      refine ⟨1975017028003323820947361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10533424149351060378385925 1975017028003323820947361)
      ·
        refine ⟨1481262771002492865710521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1975017028003323820947361 1481262771002492865710521)
        ·
          refine ⟨1110947078251869649282891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1481262771002492865710521 1110947078251869649282891)
          ·
            refine ⟨1666420617377804473924337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110947078251869649282891 1666420617377804473924337)
            ·
              refine ⟨1249815463033353355443253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666420617377804473924337 1249815463033353355443253)
              ·
                refine ⟨117170199659376877072805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1249815463033353355443253 117170199659376877072805)
                ·
                  rfl

theorem cell21_1540270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_1540270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540270 prefixEnd_1540270 := by exact prefixLift 1540270
  have htrace : WordTrace (prefixWord ++ tailWord_1540270) baseStart_1540270 baseEnd_1540270 := by
    simpa [prefixWord, tailWord_1540270, baseEnd_1540270] using wordTrace_append hprefix tailTrace_1540270
  have hstable : (prefixWord ++ tailWord_1540270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540270).length < 2 ^ (prefixWord ++ tailWord_1540270).sum := by decide
  have hdescent : baseEnd_1540270 < baseStart_1540270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540284 : List Nat := [2, 2, 2, 3, 4, 1, 1, 3, 3]
def baseStart_1540284 : Nat := 118140960795 + 1540284 * 2 ^ 59
def prefixEnd_1540284 : Nat := 4983230072969 + 3 ^ 40 * 1540284 * 2
def baseEnd_1540284 : Nat := 351513793968869717985053

theorem tailTrace_1540284 : CollatzResearch.WordTrace tailWord_1540284 prefixEnd_1540284 351513793968869717985053 := by
  unfold tailWord_1540284
  simp only [CollatzResearch.WordTrace]
  refine ⟨28089386375910801204533953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37452515167881068272711937 28089386375910801204533953)
  ·
    refine ⟨21067039781933100903400465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28089386375910801204533953 21067039781933100903400465)
    ·
      refine ⟨15800279836449825677550349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21067039781933100903400465 15800279836449825677550349)
      ·
        refine ⟨5925104938668684629081381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15800279836449825677550349 5925104938668684629081381)
        ·
          refine ⟨1110957176000378367952759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5925104938668684629081381 1110957176000378367952759)
          ·
            refine ⟨1666435764000567551929139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110957176000378367952759 1666435764000567551929139)
            ·
              refine ⟨2499653646000851327893709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666435764000567551929139 2499653646000851327893709)
              ·
                refine ⟨937370117250319247960141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2499653646000851327893709 937370117250319247960141)
                ·
                  refine ⟨351513793968869717985053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937370117250319247960141 351513793968869717985053)
                  ·
                    rfl

theorem cell21_1540284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_1540284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540284 prefixEnd_1540284 := by exact prefixLift 1540284
  have htrace : WordTrace (prefixWord ++ tailWord_1540284) baseStart_1540284 baseEnd_1540284 := by
    simpa [prefixWord, tailWord_1540284, baseEnd_1540284] using wordTrace_append hprefix tailTrace_1540284
  have hstable : (prefixWord ++ tailWord_1540284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540284).length < 2 ^ (prefixWord ++ tailWord_1540284).sum := by decide
  have hdescent : baseEnd_1540284 < baseStart_1540284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540337 : List Nat := [1, 2, 2, 2, 2, 1, 4, 7]
def baseStart_1540337 : Nat := 118140960795 + 1540337 * 2 ^ 59
def prefixEnd_1540337 : Nat := 4983230072969 + 3 ^ 40 * 1540337 * 2
def baseEnd_1540337 : Nat := 117175296430317801200537

theorem tailTrace_1540337 : CollatzResearch.WordTrace tailWord_1540337 prefixEnd_1540337 117175296430317801200537 := by
  unfold tailWord_1540337
  simp only [CollatzResearch.WordTrace]
  refine ⟨56180705820629592460747265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37453803880419728307164843 56180705820629592460747265)
  ·
    refine ⟨42135529365472194345560449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56180705820629592460747265 42135529365472194345560449)
    ·
      refine ⟨31601647024104145759170337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42135529365472194345560449 31601647024104145759170337)
      ·
        refine ⟨23701235268078109319377753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31601647024104145759170337 23701235268078109319377753)
        ·
          refine ⟨17775926451058581989533315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23701235268078109319377753 17775926451058581989533315)
          ·
            refine ⟨26663889676587872984299973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17775926451058581989533315 26663889676587872984299973)
            ·
              refine ⟨4999479314360226184556245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26663889676587872984299973 4999479314360226184556245)
              ·
                refine ⟨117175296430317801200537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4999479314360226184556245 117175296430317801200537)
                ·
                  rfl

theorem cell21_1540337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 7].length) (baseStart_1540337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540337 prefixEnd_1540337 := by exact prefixLift 1540337
  have htrace : WordTrace (prefixWord ++ tailWord_1540337) baseStart_1540337 baseEnd_1540337 := by
    simpa [prefixWord, tailWord_1540337, baseEnd_1540337] using wordTrace_append hprefix tailTrace_1540337
  have hstable : (prefixWord ++ tailWord_1540337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540337).length < 2 ^ (prefixWord ++ tailWord_1540337).sum := by decide
  have hdescent : baseEnd_1540337 < baseStart_1540337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540354 : List Nat := [3, 4, 1, 1, 2, 10]
def baseStart_1540354 : Nat := 118140960795 + 1540354 * 2 ^ 59
def prefixEnd_1540354 : Nat := 4983230072969 + 3 ^ 40 * 1540354 * 2
def baseEnd_1540354 : Nat := 13019621071206116734009

theorem tailTrace_1540354 : CollatzResearch.WordTrace tailWord_1540354 prefixEnd_1540354 13019621071206116734009 := by
  unfold tailWord_1540354
  simp only [CollatzResearch.WordTrace]
  refine ⟨14045331465392001091029029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37454217241045336242744077 14045331465392001091029029)
  ·
    refine ⟨2633499649761000204567943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14045331465392001091029029 2633499649761000204567943)
    ·
      refine ⟨3950249474641500306851915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2633499649761000204567943 3950249474641500306851915)
      ·
        refine ⟨5925374211962250460277873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3950249474641500306851915 5925374211962250460277873)
        ·
          refine ⟨4444030658971687845208405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5925374211962250460277873 4444030658971687845208405)
          ·
            refine ⟨13019621071206116734009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4444030658971687845208405 13019621071206116734009)
            ·
              rfl

theorem cell21_1540354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 10].length) (baseStart_1540354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540354 prefixEnd_1540354 := by exact prefixLift 1540354
  have htrace : WordTrace (prefixWord ++ tailWord_1540354) baseStart_1540354 baseEnd_1540354 := by
    simpa [prefixWord, tailWord_1540354, baseEnd_1540354] using wordTrace_append hprefix tailTrace_1540354
  have hstable : (prefixWord ++ tailWord_1540354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540354).length < 2 ^ (prefixWord ++ tailWord_1540354).sum := by decide
  have hdescent : baseEnd_1540354 < baseStart_1540354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540489 : List Nat := [1, 2, 1, 1, 6, 1, 1, 8]
def baseStart_1540489 : Nat := 118140960795 + 1540489 * 2 ^ 59
def prefixEnd_1540489 : Nat := 4983230072969 + 3 ^ 40 * 1540489 * 2
def baseEnd_1540489 : Nat := 117186859253944972355989

theorem tailTrace_1540489 : CollatzResearch.WordTrace tailWord_1540489 prefixEnd_1540489 117186859253944972355989 := by
  unfold tailWord_1540489
  simp only [CollatzResearch.WordTrace]
  refine ⟨56186249716078922420280521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37457499810719281613520347 56186249716078922420280521)
  ·
    refine ⟨42139687287059191815210391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56186249716078922420280521 42139687287059191815210391)
    ·
      refine ⟨63209530930588787722815587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42139687287059191815210391 63209530930588787722815587)
      ·
        refine ⟨94814296395883181584223381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63209530930588787722815587 94814296395883181584223381)
        ·
          refine ⟨4444420143557024136760471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94814296395883181584223381 4444420143557024136760471)
          ·
            refine ⟨6666630215335536205140707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444420143557024136760471 6666630215335536205140707)
            ·
              refine ⟨9999945323003304307711061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6666630215335536205140707 9999945323003304307711061)
              ·
                refine ⟨117186859253944972355989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9999945323003304307711061 117186859253944972355989)
                ·
                  rfl

theorem cell21_1540489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 8].length) (baseStart_1540489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540489 prefixEnd_1540489 := by exact prefixLift 1540489
  have htrace : WordTrace (prefixWord ++ tailWord_1540489) baseStart_1540489 baseEnd_1540489 := by
    simpa [prefixWord, tailWord_1540489, baseEnd_1540489] using wordTrace_append hprefix tailTrace_1540489
  have hstable : (prefixWord ++ tailWord_1540489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540489).length < 2 ^ (prefixWord ++ tailWord_1540489).sum := by decide
  have hdescent : baseEnd_1540489 < baseStart_1540489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540492 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 4]
def baseStart_1540492 : Nat := 118140960795 + 1540492 * 2 ^ 59
def prefixEnd_1540492 : Nat := 4983230072969 + 3 ^ 40 * 1540492 * 2
def baseEnd_1540492 : Nat := 351561262402707578517961

theorem tailTrace_1540492 : CollatzResearch.WordTrace tailWord_1540492 prefixEnd_1540492 351561262402707578517961 := by
  unfold tailWord_1540492
  simp only [CollatzResearch.WordTrace]
  refine ⟨28093179567534026966319865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37457572756712035955093153 28093179567534026966319865)
  ·
    refine ⟨21069884675650520224739899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28093179567534026966319865 21069884675650520224739899)
    ·
      refine ⟨31604827013475780337109849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21069884675650520224739899 31604827013475780337109849)
      ·
        refine ⟨23703620260106835252832387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31604827013475780337109849 23703620260106835252832387)
        ·
          refine ⟨35555430390160252879248581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23703620260106835252832387 35555430390160252879248581)
          ·
            refine ⟨6666643198155047414859109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35555430390160252879248581 6666643198155047414859109)
            ·
              refine ⟨1249995599654071390286083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6666643198155047414859109 1249995599654071390286083)
              ·
                refine ⟨1874993399481107085429125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249995599654071390286083 1874993399481107085429125)
                ·
                  refine ⟨351561262402707578517961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1874993399481107085429125 351561262402707578517961)
                  ·
                    rfl

theorem cell21_1540492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_1540492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540492 prefixEnd_1540492 := by exact prefixLift 1540492
  have htrace : WordTrace (prefixWord ++ tailWord_1540492) baseStart_1540492 baseEnd_1540492 := by
    simpa [prefixWord, tailWord_1540492, baseEnd_1540492] using wordTrace_append hprefix tailTrace_1540492
  have hstable : (prefixWord ++ tailWord_1540492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540492).length < 2 ^ (prefixWord ++ tailWord_1540492).sum := by decide
  have hdescent : baseEnd_1540492 < baseStart_1540492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540551 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 4]
def baseStart_1540551 : Nat := 118140960795 + 1540551 * 2 ^ 59
def prefixEnd_1540551 : Nat := 4983230072969 + 3 ^ 40 * 1540551 * 2
def baseEnd_1540551 : Nat := 351574727006536587034507

theorem tailTrace_1540551 : CollatzResearch.WordTrace tailWord_1540551 prefixEnd_1540551 351574727006536587034507 := by
  unfold tailWord_1540551
  simp only [CollatzResearch.WordTrace]
  refine ⟨56188511041854307009037507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37459007361236204672691671 56188511041854307009037507)
  ·
    refine ⟨84282766562781460513556261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56188511041854307009037507 84282766562781460513556261)
    ·
      refine ⟨15803018730521523846291799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84282766562781460513556261 15803018730521523846291799)
      ·
        refine ⟨23704528095782285769437699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15803018730521523846291799 23704528095782285769437699)
        ·
          refine ⟨35556792143673428654156549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23704528095782285769437699 35556792143673428654156549)
          ·
            refine ⟨6666898526938767872654353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35556792143673428654156549 6666898526938767872654353)
            ·
              refine ⟨5000173895204075904490765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6666898526938767872654353 5000173895204075904490765)
              ·
                refine ⟨1875065210701528464184037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5000173895204075904490765 1875065210701528464184037)
                ·
                  refine ⟨351574727006536587034507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1875065210701528464184037 351574727006536587034507)
                  ·
                    rfl

theorem cell21_1540551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 4].length) (baseStart_1540551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540551 prefixEnd_1540551 := by exact prefixLift 1540551
  have htrace : WordTrace (prefixWord ++ tailWord_1540551) baseStart_1540551 baseEnd_1540551 := by
    simpa [prefixWord, tailWord_1540551, baseEnd_1540551] using wordTrace_append hprefix tailTrace_1540551
  have hstable : (prefixWord ++ tailWord_1540551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540551).length < 2 ^ (prefixWord ++ tailWord_1540551).sum := by decide
  have hdescent : baseEnd_1540551 < baseStart_1540551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540647 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 5]
def baseStart_1540647 : Nat := 118140960795 + 1540647 * 2 ^ 59
def prefixEnd_1540647 : Nat := 4983230072969 + 3 ^ 40 * 1540647 * 2
def baseEnd_1540647 : Nat := 351596635514461753434311

theorem tailTrace_1540647 : CollatzResearch.WordTrace tailWord_1540647 prefixEnd_1540647 351596635514461753434311 := by
  unfold tailWord_1540647
  simp only [CollatzResearch.WordTrace]
  refine ⟨56192012449506515404532195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37461341633004343603021463 56192012449506515404532195)
  ·
    refine ⟨84288018674259773106798293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56192012449506515404532195 84288018674259773106798293)
    ·
      refine ⟨1975500437677963432190585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 84288018674259773106798293 1975500437677963432190585)
      ·
        refine ⟨1481625328258472574142939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1975500437677963432190585 1481625328258472574142939)
        ·
          refine ⟨2222437992387708861214409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481625328258472574142939 2222437992387708861214409)
          ·
            refine ⟨1666828494290781645910807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2222437992387708861214409 1666828494290781645910807)
            ·
              refine ⟨2500242741436172468866211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666828494290781645910807 2500242741436172468866211)
              ·
                refine ⟨3750364112154258703299317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500242741436172468866211 3750364112154258703299317)
                ·
                  refine ⟨351596635514461753434311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3750364112154258703299317 351596635514461753434311)
                  ·
                    rfl

theorem cell21_1540647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 5].length) (baseStart_1540647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540647 prefixEnd_1540647 := by exact prefixLift 1540647
  have htrace : WordTrace (prefixWord ++ tailWord_1540647) baseStart_1540647 baseEnd_1540647 := by
    simpa [prefixWord, tailWord_1540647, baseEnd_1540647] using wordTrace_append hprefix tailTrace_1540647
  have hstable : (prefixWord ++ tailWord_1540647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540647).length < 2 ^ (prefixWord ++ tailWord_1540647).sum := by decide
  have hdescent : baseEnd_1540647 < baseStart_1540647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540686 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_1540686 : Nat := 118140960795 + 1540686 * 2 ^ 59
def prefixEnd_1540686 : Nat := 4983230072969 + 3 ^ 40 * 1540686 * 2
def baseEnd_1540686 : Nat := 351605535845806352284231

theorem tailTrace_1540686 : CollatzResearch.WordTrace tailWord_1540686 prefixEnd_1540686 351605535845806352284231 := by
  unfold tailWord_1540686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7024179362045653133150239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37462289930910150043467941 7024179362045653133150239)
  ·
    refine ⟨10536269043068479699725359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7024179362045653133150239 10536269043068479699725359)
    ·
      refine ⟨15804403564602719549588039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10536269043068479699725359 15804403564602719549588039)
      ·
        refine ⟨23706605346904079324382059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15804403564602719549588039 23706605346904079324382059)
        ·
          refine ⟨35559908020356118986573089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23706605346904079324382059 35559908020356118986573089)
          ·
            refine ⟨26669931015267089239929817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35559908020356118986573089 26669931015267089239929817)
            ·
              refine ⟨20002448261450316929947363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26669931015267089239929817 20002448261450316929947363)
              ·
                refine ⟨30003672392175475394921045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20002448261450316929947363 30003672392175475394921045)
                ·
                  refine ⟨351605535845806352284231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30003672392175475394921045 351605535845806352284231)
                  ·
                    rfl

theorem cell21_1540686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_1540686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540686 prefixEnd_1540686 := by exact prefixLift 1540686
  have htrace : WordTrace (prefixWord ++ tailWord_1540686) baseStart_1540686 baseEnd_1540686 := by
    simpa [prefixWord, tailWord_1540686, baseEnd_1540686] using wordTrace_append hprefix tailTrace_1540686
  have hstable : (prefixWord ++ tailWord_1540686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540686).length < 2 ^ (prefixWord ++ tailWord_1540686).sum := by decide
  have hdescent : baseEnd_1540686 < baseStart_1540686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540765 : List Nat := [1, 4, 2, 1, 1, 1, 4, 4, 3]
def baseStart_1540765 : Nat := 118140960795 + 1540765 * 2 ^ 59
def prefixEnd_1540765 : Nat := 4983230072969 + 3 ^ 40 * 1540765 * 2
def baseEnd_1540765 : Nat := 351623564722119770467403

theorem tailTrace_1540765 : CollatzResearch.WordTrace tailWord_1540765 prefixEnd_1540765 351623564722119770467403 := by
  unfold tailWord_1540765
  simp only [CollatzResearch.WordTrace]
  refine ⟨56196316263079021557327749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37464210842052681038218499 56196316263079021557327749)
  ·
    refine ⟨10536809299327316541998953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56196316263079021557327749 10536809299327316541998953)
    ·
      refine ⟨7902606974495487406499215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10536809299327316541998953 7902606974495487406499215)
      ·
        refine ⟨11853910461743231109748823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7902606974495487406499215 11853910461743231109748823)
        ·
          refine ⟨17780865692614846664623235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11853910461743231109748823 17780865692614846664623235)
          ·
            refine ⟨26671298538922269996934853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17780865692614846664623235 26671298538922269996934853)
            ·
              refine ⟨5000868476047925624425285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26671298538922269996934853 5000868476047925624425285)
              ·
                refine ⟨937662839258986054579741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5000868476047925624425285 937662839258986054579741)
                ·
                  refine ⟨351623564722119770467403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937662839258986054579741 351623564722119770467403)
                  ·
                    rfl

theorem cell21_1540765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_1540765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540765 prefixEnd_1540765 := by exact prefixLift 1540765
  have htrace : WordTrace (prefixWord ++ tailWord_1540765) baseStart_1540765 baseEnd_1540765 := by
    simpa [prefixWord, tailWord_1540765, baseEnd_1540765] using wordTrace_append hprefix tailTrace_1540765
  have hstable : (prefixWord ++ tailWord_1540765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540765).length < 2 ^ (prefixWord ++ tailWord_1540765).sum := by decide
  have hdescent : baseEnd_1540765 < baseStart_1540765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540824 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_1540824 : Nat := 118140960795 + 1540824 * 2 ^ 59
def prefixEnd_1540824 : Nat := 4983230072969 + 3 ^ 40 * 1540824 * 2
def baseEnd_1540824 : Nat := 351637029325948778983949

theorem tailTrace_1540824 : CollatzResearch.WordTrace tailWord_1540824 prefixEnd_1540824 351637029325948778983949 := by
  unfold tailWord_1540824
  simp only [CollatzResearch.WordTrace]
  refine ⟨28099234084932637316862763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37465645446576849755817017 28099234084932637316862763)
  ·
    refine ⟨42148851127398955975294145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28099234084932637316862763 42148851127398955975294145)
    ·
      refine ⟨31611638345549216981470609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42148851127398955975294145 31611638345549216981470609)
      ·
        refine ⟨23708728759161912736102957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31611638345549216981470609 23708728759161912736102957)
        ·
          refine ⟨8890773284685717276038609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23708728759161912736102957 8890773284685717276038609)
          ·
            refine ⟨6668079963514287957028957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8890773284685717276038609 6668079963514287957028957)
            ·
              refine ⟨2500529986317857983885859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6668079963514287957028957 2500529986317857983885859)
              ·
                refine ⟨3750794979476786975828789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500529986317857983885859 3750794979476786975828789)
                ·
                  refine ⟨351637029325948778983949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3750794979476786975828789 351637029325948778983949)
                  ·
                    rfl

theorem cell21_1540824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_1540824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540824 prefixEnd_1540824 := by exact prefixLift 1540824
  have htrace : WordTrace (prefixWord ++ tailWord_1540824) baseStart_1540824 baseEnd_1540824 := by
    simpa [prefixWord, tailWord_1540824, baseEnd_1540824] using wordTrace_append hprefix tailTrace_1540824
  have hstable : (prefixWord ++ tailWord_1540824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540824).length < 2 ^ (prefixWord ++ tailWord_1540824).sum := by decide
  have hdescent : baseEnd_1540824 < baseStart_1540824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540883 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 5]
def baseStart_1540883 : Nat := 118140960795 + 1540883 * 2 ^ 59
def prefixEnd_1540883 : Nat := 4983230072969 + 3 ^ 40 * 1540883 * 2
def baseEnd_1540883 : Nat := 351650493929777787500495

theorem tailTrace_1540883 : CollatzResearch.WordTrace tailWord_1540883 prefixEnd_1540883 351650493929777787500495 := by
  unfold tailWord_1540883
  simp only [CollatzResearch.WordTrace]
  refine ⟨56200620076651527710123303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37467080051101018473415535 56200620076651527710123303)
  ·
    refine ⟨84300930114977291565184955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56200620076651527710123303 84300930114977291565184955)
    ·
      refine ⟨126451395172465937347777433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84300930114977291565184955 126451395172465937347777433)
      ·
        refine ⟨94838546379349453010833075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126451395172465937347777433 94838546379349453010833075)
        ·
          refine ⟨142257819569024179516249613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94838546379349453010833075 142257819569024179516249613)
          ·
            refine ⟨53346682338384067318593605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142257819569024179516249613 53346682338384067318593605)
            ·
              refine ⟨10002502938447012622236301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53346682338384067318593605 10002502938447012622236301)
              ·
                refine ⟨3750938601917629733338613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10002502938447012622236301 3750938601917629733338613)
                ·
                  refine ⟨351650493929777787500495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3750938601917629733338613 351650493929777787500495)
                  ·
                    rfl

theorem cell21_1540883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_1540883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540883 prefixEnd_1540883 := by exact prefixLift 1540883
  have htrace : WordTrace (prefixWord ++ tailWord_1540883) baseStart_1540883 baseEnd_1540883 := by
    simpa [prefixWord, tailWord_1540883, baseEnd_1540883] using wordTrace_append hprefix tailTrace_1540883
  have hstable : (prefixWord ++ tailWord_1540883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540883).length < 2 ^ (prefixWord ++ tailWord_1540883).sum := by decide
  have hdescent : baseEnd_1540883 < baseStart_1540883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540914 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1540914 : Nat := 118140960795 + 1540914 * 2 ^ 59
def prefixEnd_1540914 : Nat := 4983230072969 + 3 ^ 40 * 1540914 * 2
def baseEnd_1540914 : Nat := 351657568552128622483765

theorem tailTrace_1540914 : CollatzResearch.WordTrace tailWord_1540914 prefixEnd_1540914 351657568552128622483765 := by
  unfold tailWord_1540914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14050437684884805001125449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37467833826359480003001197 14050437684884805001125449)
  ·
    refine ⟨10537828263663603750844087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14050437684884805001125449 10537828263663603750844087)
    ·
      refine ⟨15806742395495405626266131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10537828263663603750844087 15806742395495405626266131)
      ·
        refine ⟨23710113593243108439399197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15806742395495405626266131 23710113593243108439399197)
        ·
          refine ⟨8891292597466165664774699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23710113593243108439399197 8891292597466165664774699)
          ·
            refine ⟨13336938896199248497162049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8891292597466165664774699 13336938896199248497162049)
            ·
              refine ⟨10002704172149436372871537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13336938896199248497162049 10002704172149436372871537)
              ·
                refine ⟨7502028129112077279653653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10002704172149436372871537 7502028129112077279653653)
                ·
                  refine ⟨351657568552128622483765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7502028129112077279653653 351657568552128622483765)
                  ·
                    rfl

theorem cell21_1540914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1540914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540914 prefixEnd_1540914 := by exact prefixLift 1540914
  have htrace : WordTrace (prefixWord ++ tailWord_1540914) baseStart_1540914 baseEnd_1540914 := by
    simpa [prefixWord, tailWord_1540914, baseEnd_1540914] using wordTrace_append hprefix tailTrace_1540914
  have hstable : (prefixWord ++ tailWord_1540914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540914).length < 2 ^ (prefixWord ++ tailWord_1540914).sum := by decide
  have hdescent : baseEnd_1540914 < baseStart_1540914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540917 : List Nat := [1, 3, 3, 1, 3, 1, 1, 5, 3]
def baseStart_1540917 : Nat := 118140960795 + 1540917 * 2 ^ 59
def prefixEnd_1540917 : Nat := 4983230072969 + 3 ^ 40 * 1540917 * 2
def baseEnd_1540917 : Nat := 351658253193001283933759

theorem tailTrace_1540917 : CollatzResearch.WordTrace tailWord_1540917 prefixEnd_1540917 351658253193001283933759 := by
  unfold tailWord_1540917
  simp only [CollatzResearch.WordTrace]
  refine ⟨56201860158528351516861005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37467906772352234344574003 56201860158528351516861005)
  ·
    refine ⟨21075697559448131818822877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56201860158528351516861005 21075697559448131818822877)
    ·
      refine ⟨7903386584793049432058579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21075697559448131818822877 7903386584793049432058579)
      ·
        refine ⟨11855079877189574148087869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7903386584793049432058579 11855079877189574148087869)
        ·
          refine ⟨4445654953946090305532951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11855079877189574148087869 4445654953946090305532951)
          ·
            refine ⟨6668482430919135458299427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445654953946090305532951 6668482430919135458299427)
            ·
              refine ⟨10002723646378703187449141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6668482430919135458299427 10002723646378703187449141)
              ·
                refine ⟨937755341848003423823357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10002723646378703187449141 937755341848003423823357)
                ·
                  refine ⟨351658253193001283933759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937755341848003423823357 351658253193001283933759)
                  ·
                    rfl

theorem cell21_1540917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_1540917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540917 prefixEnd_1540917 := by exact prefixLift 1540917
  have htrace : WordTrace (prefixWord ++ tailWord_1540917) baseStart_1540917 baseEnd_1540917 := by
    simpa [prefixWord, tailWord_1540917, baseEnd_1540917] using wordTrace_append hprefix tailTrace_1540917
  have hstable : (prefixWord ++ tailWord_1540917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540917).length < 2 ^ (prefixWord ++ tailWord_1540917).sum := by decide
  have hdescent : baseEnd_1540917 < baseStart_1540917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540959 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 5]
def baseStart_1540959 : Nat := 118140960795 + 1540959 * 2 ^ 59
def prefixEnd_1540959 : Nat := 4983230072969 + 3 ^ 40 * 1540959 * 2
def baseEnd_1540959 : Nat := 351667838165218544233673

theorem tailTrace_1540959 : CollatzResearch.WordTrace tailWord_1540959 prefixEnd_1540959 351667838165218544233673 := by
  unfold tailWord_1540959
  simp only [CollatzResearch.WordTrace]
  refine ⟨56203392024376192689889931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37468928016250795126593287 56203392024376192689889931)
  ·
    refine ⟨84305088036564289034834897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56203392024376192689889931 84305088036564289034834897)
    ·
      refine ⟨63228816027423216776126173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84305088036564289034834897 63228816027423216776126173)
      ·
        refine ⟨23710806010283706291047315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63228816027423216776126173 23710806010283706291047315)
        ·
          refine ⟨35566209015425559436570973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23710806010283706291047315 35566209015425559436570973)
          ·
            refine ⟨13337328380784584788714115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35566209015425559436570973 13337328380784584788714115)
            ·
              refine ⟨20005992571176877183071173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13337328380784584788714115 20005992571176877183071173)
              ·
                refine ⟨3751123607095664471825845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20005992571176877183071173 3751123607095664471825845)
                ·
                  refine ⟨351667838165218544233673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3751123607095664471825845 351667838165218544233673)
                  ·
                    rfl

theorem cell21_1540959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_1540959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540959 prefixEnd_1540959 := by exact prefixLift 1540959
  have htrace : WordTrace (prefixWord ++ tailWord_1540959) baseStart_1540959 baseEnd_1540959 := by
    simpa [prefixWord, tailWord_1540959, baseEnd_1540959] using wordTrace_append hprefix tailTrace_1540959
  have hstable : (prefixWord ++ tailWord_1540959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540959).length < 2 ^ (prefixWord ++ tailWord_1540959).sum := by decide
  have hdescent : baseEnd_1540959 < baseStart_1540959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540962 : List Nat := [3, 3, 2, 1, 3, 1, 1, 7]
def baseStart_1540962 : Nat := 118140960795 + 1540962 * 2 ^ 59
def prefixEnd_1540962 : Nat := 4983230072969 + 3 ^ 40 * 1540962 * 2
def baseEnd_1540962 : Nat := 117222840935363735227889

theorem tailTrace_1540962 : CollatzResearch.WordTrace tailWord_1540962 prefixEnd_1540962 117222840935363735227889 := by
  unfold tailWord_1540962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14050875360841331050562285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37469000962243549468166093 14050875360841331050562285)
  ·
    refine ⟨5269078260315499143960857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14050875360841331050562285 5269078260315499143960857)
    ·
      refine ⟨3951808695236624357970643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5269078260315499143960857 3951808695236624357970643)
      ·
        refine ⟨5927713042854936536955965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3951808695236624357970643 5927713042854936536955965)
        ·
          refine ⟨2222892391070601201358487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5927713042854936536955965 2222892391070601201358487)
          ·
            refine ⟨3334338586605901802037731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222892391070601201358487 3334338586605901802037731)
            ·
              refine ⟨5001507879908852703056597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334338586605901802037731 5001507879908852703056597)
              ·
                refine ⟨117222840935363735227889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5001507879908852703056597 117222840935363735227889)
                ·
                  rfl

theorem cell21_1540962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_1540962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1540962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1540962 prefixEnd_1540962 := by exact prefixLift 1540962
  have htrace : WordTrace (prefixWord ++ tailWord_1540962) baseStart_1540962 baseEnd_1540962 := by
    simpa [prefixWord, tailWord_1540962, baseEnd_1540962] using wordTrace_append hprefix tailTrace_1540962
  have hstable : (prefixWord ++ tailWord_1540962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540962).length < 2 ^ (prefixWord ++ tailWord_1540962).sum := by decide
  have hdescent : baseEnd_1540962 < baseStart_1540962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541004 : List Nat := [2, 2, 1, 2, 1, 2, 3, 8]
def baseStart_1541004 : Nat := 118140960795 + 1541004 * 2 ^ 59
def prefixEnd_1541004 : Nat := 4983230072969 + 3 ^ 40 * 1541004 * 2
def baseEnd_1541004 : Nat := 117226035926102821994527

theorem tailTrace_1541004 : CollatzResearch.WordTrace tailWord_1541004 prefixEnd_1541004 117226035926102821994527 := by
  unfold tailWord_1541004
  simp only [CollatzResearch.WordTrace]
  refine ⟨28102516654606582687639033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37470022206142110250185377 28102516654606582687639033)
  ·
    refine ⟨21076887490954937015729275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28102516654606582687639033 21076887490954937015729275)
    ·
      refine ⟨31615331236432405523593913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21076887490954937015729275 31615331236432405523593913)
      ·
        refine ⟨23711498427324304142695435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31615331236432405523593913 23711498427324304142695435)
        ·
          refine ⟨35567247640986456214043153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23711498427324304142695435 35567247640986456214043153)
          ·
            refine ⟨26675435730739842160532365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35567247640986456214043153 26675435730739842160532365)
            ·
              refine ⟨10003288399027440810199637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26675435730739842160532365 10003288399027440810199637)
              ·
                refine ⟨117226035926102821994527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10003288399027440810199637 117226035926102821994527)
                ·
                  rfl

theorem cell21_1541004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_1541004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541004 prefixEnd_1541004 := by exact prefixLift 1541004
  have htrace : WordTrace (prefixWord ++ tailWord_1541004) baseStart_1541004 baseEnd_1541004 := by
    simpa [prefixWord, tailWord_1541004, baseEnd_1541004] using wordTrace_append hprefix tailTrace_1541004
  have hstable : (prefixWord ++ tailWord_1541004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541004).length < 2 ^ (prefixWord ++ tailWord_1541004).sum := by decide
  have hdescent : baseEnd_1541004 < baseStart_1541004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541044 : List Nat := [2, 5, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1541044 : Nat := 118140960795 + 1541044 * 2 ^ 59
def prefixEnd_1541044 : Nat := 4983230072969 + 3 ^ 40 * 1541044 * 2
def baseEnd_1541044 : Nat := 351687236323277285316833

theorem tailTrace_1541044 : CollatzResearch.WordTrace tailWord_1541044 prefixEnd_1541044 351687236323277285316833 := by
  unfold tailWord_1541044
  simp only [CollatzResearch.WordTrace]
  refine ⟨28103246114534126103367093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37470994819378834804489457 28103246114534126103367093)
  ·
    refine ⟨2634679323237574322190665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28103246114534126103367093 2634679323237574322190665)
    ·
      refine ⟨1976009492428180741642999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2634679323237574322190665 1976009492428180741642999)
      ·
        refine ⟨2964014238642271112464499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976009492428180741642999 2964014238642271112464499)
        ·
          refine ⟨4446021357963406668696749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964014238642271112464499 4446021357963406668696749)
          ·
            refine ⟨1667258009236277500761281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4446021357963406668696749 1667258009236277500761281)
            ·
              refine ⟨1250443506927208125570961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667258009236277500761281 1250443506927208125570961)
              ·
                refine ⟨937832630195406094178221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250443506927208125570961 937832630195406094178221)
                ·
                  refine ⟨351687236323277285316833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937832630195406094178221 351687236323277285316833)
                  ·
                    rfl

theorem cell21_1541044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1541044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541044 prefixEnd_1541044 := by exact prefixLift 1541044
  have htrace : WordTrace (prefixWord ++ tailWord_1541044) baseStart_1541044 baseEnd_1541044 := by
    simpa [prefixWord, tailWord_1541044, baseEnd_1541044] using wordTrace_append hprefix tailTrace_1541044
  have hstable : (prefixWord ++ tailWord_1541044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541044).length < 2 ^ (prefixWord ++ tailWord_1541044).sum := by decide
  have hdescent : baseEnd_1541044 < baseStart_1541044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541159 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 6]
def baseStart_1541159 : Nat := 118140960795 + 1541159 * 2 ^ 59
def prefixEnd_1541159 : Nat := 4983230072969 + 3 ^ 40 * 1541159 * 2
def baseEnd_1541159 : Nat := 351713480890062640899931

theorem tailTrace_1541159 : CollatzResearch.WordTrace tailWord_1541159 prefixEnd_1541159 351713480890062640899931 := by
  unfold tailWord_1541159
  simp only [CollatzResearch.WordTrace]
  refine ⟨56210686623651626847170531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37473791082434417898113687 56210686623651626847170531)
  ·
    refine ⟨84316029935477440270755797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56210686623651626847170531 84316029935477440270755797)
    ·
      refine ⟨1976156951612752506345839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 84316029935477440270755797 1976156951612752506345839)
      ·
        refine ⟨2964235427419128759518759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976156951612752506345839 2964235427419128759518759)
        ·
          refine ⟨4446353141128693139278139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964235427419128759518759 4446353141128693139278139)
          ·
            refine ⟨6669529711693039708917209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446353141128693139278139 6669529711693039708917209)
            ·
              refine ⟨5002147283769779781687907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6669529711693039708917209 5002147283769779781687907)
              ·
                refine ⟨7503220925654669672531861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002147283769779781687907 7503220925654669672531861)
                ·
                  refine ⟨351713480890062640899931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7503220925654669672531861 351713480890062640899931)
                  ·
                    rfl

theorem cell21_1541159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 6].length) (baseStart_1541159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541159 prefixEnd_1541159 := by exact prefixLift 1541159
  have htrace : WordTrace (prefixWord ++ tailWord_1541159) baseStart_1541159 baseEnd_1541159 := by
    simpa [prefixWord, tailWord_1541159, baseEnd_1541159] using wordTrace_append hprefix tailTrace_1541159
  have hstable : (prefixWord ++ tailWord_1541159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541159).length < 2 ^ (prefixWord ++ tailWord_1541159).sum := by decide
  have hdescent : baseEnd_1541159 < baseStart_1541159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541162 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 5]
def baseStart_1541162 : Nat := 118140960795 + 1541162 * 2 ^ 59
def prefixEnd_1541162 : Nat := 4983230072969 + 3 ^ 40 * 1541162 * 2
def baseEnd_1541162 : Nat := 351714165530935302349925

theorem tailTrace_1541162 : CollatzResearch.WordTrace tailWord_1541162 prefixEnd_1541162 351714165530935302349925 := by
  unfold tailWord_1541162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14052699010660189589882435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37473864028427172239686493 14052699010660189589882435)
  ·
    refine ⟨21079048515990284384823653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14052699010660189589882435 21079048515990284384823653)
    ·
      refine ⟨3952321596748178322154435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21079048515990284384823653 3952321596748178322154435)
      ·
        refine ⟨5928482395122267483231653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3952321596748178322154435 5928482395122267483231653)
        ·
          refine ⟨1111590449085425153105935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5928482395122267483231653 1111590449085425153105935)
          ·
            refine ⟨1667385673628137729658903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111590449085425153105935 1667385673628137729658903)
            ·
              refine ⟨2501078510442206594488355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667385673628137729658903 2501078510442206594488355)
              ·
                refine ⟨3751617765663309891732533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501078510442206594488355 3751617765663309891732533)
                ·
                  refine ⟨351714165530935302349925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3751617765663309891732533 351714165530935302349925)
                  ·
                    rfl

theorem cell21_1541162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_1541162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541162 prefixEnd_1541162 := by exact prefixLift 1541162
  have htrace : WordTrace (prefixWord ++ tailWord_1541162) baseStart_1541162 baseEnd_1541162 := by
    simpa [prefixWord, tailWord_1541162, baseEnd_1541162] using wordTrace_append hprefix tailTrace_1541162
  have hstable : (prefixWord ++ tailWord_1541162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541162).length < 2 ^ (prefixWord ++ tailWord_1541162).sum := by decide
  have hdescent : baseEnd_1541162 < baseStart_1541162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541176 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 4]
def baseStart_1541176 : Nat := 118140960795 + 1541176 * 2 ^ 59
def prefixEnd_1541176 : Nat := 4983230072969 + 3 ^ 40 * 1541176 * 2
def baseEnd_1541176 : Nat := 351717360521674389116563

theorem tailTrace_1541176 : CollatzResearch.WordTrace tailWord_1541176 prefixEnd_1541176 351717360521674389116563 := by
  unfold tailWord_1541176
  simp only [CollatzResearch.WordTrace]
  refine ⟨28105653332295019375269691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37474204443060025833692921 28105653332295019375269691)
  ·
    refine ⟨42158479998442529062904537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28105653332295019375269691 42158479998442529062904537)
    ·
      refine ⟨31618859998831896797178403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42158479998442529062904537 31618859998831896797178403)
      ·
        refine ⟨47428289998247845195767605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31618859998831896797178403 47428289998247845195767605)
        ·
          refine ⟨4446402187335735487103213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47428289998247845195767605 4446402187335735487103213)
          ·
            refine ⟨1667400820250900807663705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4446402187335735487103213 1667400820250900807663705)
            ·
              refine ⟨1250550615188175605747779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667400820250900807663705 1250550615188175605747779)
              ·
                refine ⟨1875825922782263408621669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250550615188175605747779 1875825922782263408621669)
                ·
                  refine ⟨351717360521674389116563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1875825922782263408621669 351717360521674389116563)
                  ·
                    rfl

theorem cell21_1541176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_1541176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541176 prefixEnd_1541176 := by exact prefixLift 1541176
  have htrace : WordTrace (prefixWord ++ tailWord_1541176) baseStart_1541176 baseEnd_1541176 := by
    simpa [prefixWord, tailWord_1541176, baseEnd_1541176] using wordTrace_append hprefix tailTrace_1541176
  have hstable : (prefixWord ++ tailWord_1541176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541176).length < 2 ^ (prefixWord ++ tailWord_1541176).sum := by decide
  have hdescent : baseEnd_1541176 < baseStart_1541176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541190 : List Nat := [6, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1541190 : Nat := 118140960795 + 1541190 * 2 ^ 59
def prefixEnd_1541190 : Nat := 4983230072969 + 3 ^ 40 * 1541190 * 2
def baseEnd_1541190 : Nat := 117240185170804491961067

theorem tailTrace_1541190 : CollatzResearch.WordTrace tailWord_1541190 prefixEnd_1541190 117240185170804491961067 := by
  unfold tailWord_1541190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756619290204353723173407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37474544857692879427699349 1756619290204353723173407)
  ·
    refine ⟨2634928935306530584760111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1756619290204353723173407 2634928935306530584760111)
    ·
      refine ⟨3952393402959795877140167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2634928935306530584760111 3952393402959795877140167)
      ·
        refine ⟨5928590104439693815710251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3952393402959795877140167 5928590104439693815710251)
        ·
          refine ⟨8892885156659540723565377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5928590104439693815710251 8892885156659540723565377)
          ·
            refine ⟨6669663867494655542674033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8892885156659540723565377 6669663867494655542674033)
            ·
              refine ⟨5002247900620991657005525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6669663867494655542674033 5002247900620991657005525)
              ·
                refine ⟨117240185170804491961067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5002247900620991657005525 117240185170804491961067)
                ·
                  rfl

theorem cell21_1541190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1541190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541190 prefixEnd_1541190 := by exact prefixLift 1541190
  have htrace : WordTrace (prefixWord ++ tailWord_1541190) baseStart_1541190 baseEnd_1541190 := by
    simpa [prefixWord, tailWord_1541190, baseEnd_1541190] using wordTrace_append hprefix tailTrace_1541190
  have hstable : (prefixWord ++ tailWord_1541190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541190).length < 2 ^ (prefixWord ++ tailWord_1541190).sum := by decide
  have hdescent : baseEnd_1541190 < baseStart_1541190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541201 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 8]
def baseStart_1541201 : Nat := 118140960795 + 1541201 * 2 ^ 59
def prefixEnd_1541201 : Nat := 4983230072969 + 3 ^ 40 * 1541201 * 2
def baseEnd_1541201 : Nat := 351723065862279901199845

theorem tailTrace_1541201 : CollatzResearch.WordTrace tailWord_1541201 prefixEnd_1541201 351723065862279901199845 := by
  unfold tailWord_1541201
  simp only [CollatzResearch.WordTrace]
  refine ⟨56212218489499468020199457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37474812326332978680132971 56212218489499468020199457)
  ·
    refine ⟨42159163867124601015149593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56212218489499468020199457 42159163867124601015149593)
    ·
      refine ⟨31619372900343450761362195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42159163867124601015149593 31619372900343450761362195)
      ·
        refine ⟨47429059350515176142043293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31619372900343450761362195 47429059350515176142043293)
        ·
          refine ⟨17785897256443191053266235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47429059350515176142043293 17785897256443191053266235)
          ·
            refine ⟨26678845884664786579899353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17785897256443191053266235 26678845884664786579899353)
            ·
              refine ⟨20009134413498589934924515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26678845884664786579899353 20009134413498589934924515)
              ·
                refine ⟨30013701620247884902386773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20009134413498589934924515 30013701620247884902386773)
                ·
                  refine ⟨351723065862279901199845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30013701620247884902386773 351723065862279901199845)
                  ·
                    rfl

theorem cell21_1541201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_1541201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541201 prefixEnd_1541201 := by exact prefixLift 1541201
  have htrace : WordTrace (prefixWord ++ tailWord_1541201) baseStart_1541201 baseEnd_1541201 := by
    simpa [prefixWord, tailWord_1541201, baseEnd_1541201] using wordTrace_append hprefix tailTrace_1541201
  have hstable : (prefixWord ++ tailWord_1541201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541201).length < 2 ^ (prefixWord ++ tailWord_1541201).sum := by decide
  have hdescent : baseEnd_1541201 < baseStart_1541201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541280 : List Nat := [2, 1, 1, 4, 2, 1, 1, 6, 3]
def baseStart_1541280 : Nat := 118140960795 + 1541280 * 2 ^ 59
def prefixEnd_1541280 : Nat := 4983230072969 + 3 ^ 40 * 1541280 * 2
def baseEnd_1541280 : Nat := 351741094738593319383017

theorem tailTrace_1541280 : CollatzResearch.WordTrace tailWord_1541280 prefixEnd_1541280 351741094738593319383017 := by
  unfold tailWord_1541280
  simp only [CollatzResearch.WordTrace]
  refine ⟨28107549928106632256162647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37476733237475509674883529 28107549928106632256162647)
  ·
    refine ⟨42161324892159948384243971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28107549928106632256162647 42161324892159948384243971)
    ·
      refine ⟨63241987338239922576365957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42161324892159948384243971 63241987338239922576365957)
      ·
        refine ⟨11857872625919985483068617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63241987338239922576365957 11857872625919985483068617)
        ·
          refine ⟨8893404469439989112301463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11857872625919985483068617 8893404469439989112301463)
          ·
            refine ⟨13340106704159983668452195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8893404469439989112301463 13340106704159983668452195)
            ·
              refine ⟨20010160056239975502678293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13340106704159983668452195 20010160056239975502678293)
              ·
                refine ⟨937976252636248851688045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20010160056239975502678293 937976252636248851688045)
                ·
                  refine ⟨351741094738593319383017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937976252636248851688045 351741094738593319383017)
                  ·
                    rfl

theorem cell21_1541280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 3].length) (baseStart_1541280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541280 prefixEnd_1541280 := by exact prefixLift 1541280
  have htrace : WordTrace (prefixWord ++ tailWord_1541280) baseStart_1541280 baseEnd_1541280 := by
    simpa [prefixWord, tailWord_1541280, baseEnd_1541280] using wordTrace_append hprefix tailTrace_1541280
  have hstable : (prefixWord ++ tailWord_1541280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541280).length < 2 ^ (prefixWord ++ tailWord_1541280).sum := by decide
  have hdescent : baseEnd_1541280 < baseStart_1541280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541384 : List Nat := [2, 1, 3, 2, 4, 9]
def baseStart_1541384 : Nat := 118140960795 + 1541384 * 2 ^ 59
def prefixEnd_1541384 : Nat := 4983230072969 + 3 ^ 40 * 1541384 * 2
def baseEnd_1541384 : Nat := 13028326998352305542573

theorem tailTrace_1541384 : CollatzResearch.WordTrace tailWord_1541384 prefixEnd_1541384 13028326998352305542573 := by
  unfold tailWord_1541384
  simp only [CollatzResearch.WordTrace]
  refine ⟨28109446523918245137055603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37479262031890993516074137 28109446523918245137055603)
  ·
    refine ⟨42164169785877367705583405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28109446523918245137055603 42164169785877367705583405)
    ·
      refine ⟨15811563669704012889593777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42164169785877367705583405 15811563669704012889593777)
      ·
        refine ⟨11858672752278009667195333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15811563669704012889593777 11858672752278009667195333)
        ·
          refine ⟨2223501141052126812599125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11858672752278009667195333 2223501141052126812599125)
          ·
            refine ⟨13028326998352305542573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2223501141052126812599125 13028326998352305542573)
            ·
              rfl

theorem cell21_1541384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 9].length) (baseStart_1541384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541384 prefixEnd_1541384 := by exact prefixLift 1541384
  have htrace : WordTrace (prefixWord ++ tailWord_1541384) baseStart_1541384 baseEnd_1541384 := by
    simpa [prefixWord, tailWord_1541384, baseEnd_1541384] using wordTrace_append hprefix tailTrace_1541384
  have hstable : (prefixWord ++ tailWord_1541384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541384).length < 2 ^ (prefixWord ++ tailWord_1541384).sum := by decide
  have hdescent : baseEnd_1541384 < baseStart_1541384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541390 : List Nat := [4, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_1541390 : Nat := 118140960795 + 1541390 * 2 ^ 59
def prefixEnd_1541390 : Nat := 4983230072969 + 3 ^ 40 * 1541390 * 2
def baseEnd_1541390 : Nat := 351766198237257572549459

theorem tailTrace_1541390 : CollatzResearch.WordTrace tailWord_1541390 prefixEnd_1541390 351766198237257572549459 := by
  unfold tailWord_1541390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7027388985726844162353703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37479407923876502199219749 7027388985726844162353703)
  ·
    refine ⟨10541083478590266243530555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7027388985726844162353703 10541083478590266243530555)
    ·
      refine ⟨15811625217885399365295833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10541083478590266243530555 15811625217885399365295833)
      ·
        refine ⟨11858718913414049523971875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15811625217885399365295833 11858718913414049523971875)
        ·
          refine ⟨17788078370121074285957813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11858718913414049523971875 17788078370121074285957813)
          ·
            refine ⟨1667632347198850714308545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17788078370121074285957813 1667632347198850714308545)
            ·
              refine ⟨1250724260399138035731409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667632347198850714308545 1250724260399138035731409)
              ·
                refine ⟨938043195299353526798557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250724260399138035731409 938043195299353526798557)
                ·
                  refine ⟨351766198237257572549459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938043195299353526798557 351766198237257572549459)
                  ·
                    rfl

theorem cell21_1541390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_1541390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541390 prefixEnd_1541390 := by exact prefixLift 1541390
  have htrace : WordTrace (prefixWord ++ tailWord_1541390) baseStart_1541390 baseEnd_1541390 := by
    simpa [prefixWord, tailWord_1541390, baseEnd_1541390] using wordTrace_append hprefix tailTrace_1541390
  have hstable : (prefixWord ++ tailWord_1541390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541390).length < 2 ^ (prefixWord ++ tailWord_1541390).sum := by decide
  have hdescent : baseEnd_1541390 < baseStart_1541390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541418 : List Nat := [3, 1, 4, 2, 1, 2, 3, 5]
def baseStart_1541418 : Nat := 118140960795 + 1541418 * 2 ^ 59
def prefixEnd_1541418 : Nat := 4983230072969 + 3 ^ 40 * 1541418 * 2
def baseEnd_1541418 : Nat := 117257529406245248694245

theorem tailTrace_1541418 : CollatzResearch.WordTrace tailWord_1541418 prefixEnd_1541418 117257529406245248694245 := by
  unfold tailWord_1541418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14055033282428328520212227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37480088753142209387232605 14055033282428328520212227)
  ·
    refine ⟨21082549923642492780318341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14055033282428328520212227 21082549923642492780318341)
    ·
      refine ⟨3952978110682967396309689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21082549923642492780318341 3952978110682967396309689)
      ·
        refine ⟨2964733583012225547232267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3952978110682967396309689 2964733583012225547232267)
        ·
          refine ⟨4447100374518338320848401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964733583012225547232267 4447100374518338320848401)
          ·
            refine ⟨3335325280888753740636301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4447100374518338320848401 3335325280888753740636301)
            ·
              refine ⟨1250746980333282652738613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3335325280888753740636301 1250746980333282652738613)
              ·
                refine ⟨117257529406245248694245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1250746980333282652738613 117257529406245248694245)
                ·
                  rfl

theorem cell21_1541418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_1541418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541418 prefixEnd_1541418 := by exact prefixLift 1541418
  have htrace : WordTrace (prefixWord ++ tailWord_1541418) baseStart_1541418 baseEnd_1541418 := by
    simpa [prefixWord, tailWord_1541418, baseEnd_1541418] using wordTrace_append hprefix tailTrace_1541418
  have hstable : (prefixWord ++ tailWord_1541418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541418).length < 2 ^ (prefixWord ++ tailWord_1541418).sum := by decide
  have hdescent : baseEnd_1541418 < baseStart_1541418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541460 : List Nat := [2, 4, 1, 1, 2, 1, 2, 8]
def baseStart_1541460 : Nat := 118140960795 + 1541460 * 2 ^ 59
def prefixEnd_1541460 : Nat := 4983230072969 + 3 ^ 40 * 1541460 * 2
def baseEnd_1541460 : Nat := 117260724396984335460883

theorem tailTrace_1541460 : CollatzResearch.WordTrace tailWord_1541460 prefixEnd_1541460 117260724396984335460883 := by
  unfold tailWord_1541460
  simp only [CollatzResearch.WordTrace]
  refine ⟨28110832497780577626938917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37481109997040770169251889 28110832497780577626938917)
  ·
    refine ⟨5270781093333858305051047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28110832497780577626938917 5270781093333858305051047)
    ·
      refine ⟨7906171640000787457576571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5270781093333858305051047 7906171640000787457576571)
      ·
        refine ⟨11859257460001181186364857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7906171640000787457576571 11859257460001181186364857)
        ·
          refine ⟨8894443095000885889773643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11859257460001181186364857 8894443095000885889773643)
          ·
            refine ⟨13341664642501328834660465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8894443095000885889773643 13341664642501328834660465)
            ·
              refine ⟨10006248481875996625995349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13341664642501328834660465 10006248481875996625995349)
              ·
                refine ⟨117260724396984335460883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10006248481875996625995349 117260724396984335460883)
                ·
                  rfl

theorem cell21_1541460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_1541460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541460 prefixEnd_1541460 := by exact prefixLift 1541460
  have htrace : WordTrace (prefixWord ++ tailWord_1541460) baseStart_1541460 baseEnd_1541460 := by
    simpa [prefixWord, tailWord_1541460, baseEnd_1541460] using wordTrace_append hprefix tailTrace_1541460
  have hstable : (prefixWord ++ tailWord_1541460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541460).length < 2 ^ (prefixWord ++ tailWord_1541460).sum := by decide
  have hdescent : baseEnd_1541460 < baseStart_1541460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541463 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 4]
def baseStart_1541463 : Nat := 118140960795 + 1541463 * 2 ^ 59
def prefixEnd_1541463 : Nat := 4983230072969 + 3 ^ 40 * 1541463 * 2
def baseEnd_1541463 : Nat := 351782857831825667832643

theorem tailTrace_1541463 : CollatzResearch.WordTrace tailWord_1541463 prefixEnd_1541463 351782857831825667832643 := by
  unfold tailWord_1541463
  simp only [CollatzResearch.WordTrace]
  refine ⟨56221774414550286766237043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37481182943033524510824695 56221774414550286766237043)
  ·
    refine ⟨84332661621825430149355565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56221774414550286766237043 84332661621825430149355565)
    ·
      refine ⟨31624748108184536306008337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84332661621825430149355565 31624748108184536306008337)
      ·
        refine ⟨23718561081138402229506253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31624748108184536306008337 23718561081138402229506253)
        ·
          refine ⟨8894460405426900836064845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23718561081138402229506253 8894460405426900836064845)
          ·
            refine ⟨3335422652035087813524317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8894460405426900836064845 3335422652035087813524317)
            ·
              refine ⟨1250783494513157930071619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3335422652035087813524317 1250783494513157930071619)
              ·
                refine ⟨1876175241769736895107429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250783494513157930071619 1876175241769736895107429)
                ·
                  refine ⟨351782857831825667832643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876175241769736895107429 351782857831825667832643)
                  ·
                    rfl

theorem cell21_1541463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 4].length) (baseStart_1541463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541463 prefixEnd_1541463 := by exact prefixLift 1541463
  have htrace : WordTrace (prefixWord ++ tailWord_1541463) baseStart_1541463 baseEnd_1541463 := by
    simpa [prefixWord, tailWord_1541463, baseEnd_1541463] using wordTrace_append hprefix tailTrace_1541463
  have hstable : (prefixWord ++ tailWord_1541463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541463).length < 2 ^ (prefixWord ++ tailWord_1541463).sum := by decide
  have hdescent : baseEnd_1541463 < baseStart_1541463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541469 : List Nat := [1, 4, 5, 1, 2, 1, 2, 5]
def baseStart_1541469 : Nat := 118140960795 + 1541469 * 2 ^ 59
def prefixEnd_1541469 : Nat := 4983230072969 + 3 ^ 40 * 1541469 * 2
def baseEnd_1541469 : Nat := 117261409037856996910877

theorem tailTrace_1541469 : CollatzResearch.WordTrace tailWord_1541469 prefixEnd_1541469 117261409037856996910877 := by
  unfold tailWord_1541469
  simp only [CollatzResearch.WordTrace]
  refine ⟨56221993252528549790955461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37481328835019033193970307 56221993252528549790955461)
  ·
    refine ⟨10541623734849103085804149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56221993252528549790955461 10541623734849103085804149)
    ·
      refine ⟨988277225142103414294139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10541623734849103085804149 988277225142103414294139)
      ·
        refine ⟨1482415837713155121441209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988277225142103414294139 1482415837713155121441209)
        ·
          refine ⟨1111811878284866341080907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1482415837713155121441209 1111811878284866341080907)
          ·
            refine ⟨1667717817427299511621361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111811878284866341080907 1667717817427299511621361)
            ·
              refine ⟨1250788363070474633716021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667717817427299511621361 1250788363070474633716021)
              ·
                refine ⟨117261409037856996910877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1250788363070474633716021 117261409037856996910877)
                ·
                  rfl

theorem cell21_1541469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 5].length) (baseStart_1541469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541469 prefixEnd_1541469 := by exact prefixLift 1541469
  have htrace : WordTrace (prefixWord ++ tailWord_1541469) baseStart_1541469 baseEnd_1541469 := by
    simpa [prefixWord, tailWord_1541469, baseEnd_1541469] using wordTrace_append hprefix tailTrace_1541469
  have hstable : (prefixWord ++ tailWord_1541469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541469).length < 2 ^ (prefixWord ++ tailWord_1541469).sum := by decide
  have hdescent : baseEnd_1541469 < baseStart_1541469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541508 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1541508 : Nat := 118140960795 + 1541508 * 2 ^ 59
def prefixEnd_1541508 : Nat := 4983230072969 + 3 ^ 40 * 1541508 * 2
def baseEnd_1541508 : Nat := 351793127444915589582551

theorem tailTrace_1541508 : CollatzResearch.WordTrace tailWord_1541508 prefixEnd_1541508 351793127444915589582551 := by
  unfold tailWord_1541508
  simp only [CollatzResearch.WordTrace]
  refine ⟨28111707849693629725812589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37482277132924839634416785 28111707849693629725812589)
  ·
    refine ⟨10541890443635111147179721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28111707849693629725812589 10541890443635111147179721)
    ·
      refine ⟨7906417832726333360384791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10541890443635111147179721 7906417832726333360384791)
      ·
        refine ⟨11859626749089500040577187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7906417832726333360384791 11859626749089500040577187)
        ·
          refine ⟨17789440123634250060865781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11859626749089500040577187 17789440123634250060865781)
          ·
            refine ⟨1667760011590710943206167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17789440123634250060865781 1667760011590710943206167)
            ·
              refine ⟨2501640017386066414809251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667760011590710943206167 2501640017386066414809251)
              ·
                refine ⟨3752460026079099622213877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501640017386066414809251 3752460026079099622213877)
                ·
                  refine ⟨351793127444915589582551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3752460026079099622213877 351793127444915589582551)
                  ·
                    rfl

theorem cell21_1541508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1541508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541508 prefixEnd_1541508 := by exact prefixLift 1541508
  have htrace : WordTrace (prefixWord ++ tailWord_1541508) baseStart_1541508 baseEnd_1541508 := by
    simpa [prefixWord, tailWord_1541508, baseEnd_1541508] using wordTrace_append hprefix tailTrace_1541508
  have hstable : (prefixWord ++ tailWord_1541508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541508).length < 2 ^ (prefixWord ++ tailWord_1541508).sum := by decide
  have hdescent : baseEnd_1541508 < baseStart_1541508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541646 : List Nat := [4, 1, 1, 2, 4, 2, 2, 5]
def baseStart_1541646 : Nat := 118140960795 + 1541646 * 2 ^ 59
def prefixEnd_1541646 : Nat := 4983230072969 + 3 ^ 40 * 1541646 * 2
def baseEnd_1541646 : Nat := 117274873641686005427423

theorem tailTrace_1541646 : CollatzResearch.WordTrace tailWord_1541646 prefixEnd_1541646 117274873641686005427423 := by
  unfold tailWord_1541646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7028556121610913627518599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37485632648591539346765861 7028556121610913627518599)
  ·
    refine ⟨10542834182416370441277899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7028556121610913627518599 10542834182416370441277899)
    ·
      refine ⟨15814251273624555661916849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10542834182416370441277899 15814251273624555661916849)
      ·
        refine ⟨11860688455218416746437637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15814251273624555661916849 11860688455218416746437637)
        ·
          refine ⟨2223879085353453139957057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11860688455218416746437637 2223879085353453139957057)
          ·
            refine ⟨1667909314015089854967793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2223879085353453139957057 1667909314015089854967793)
            ·
              refine ⟨1250931985511317391225845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667909314015089854967793 1250931985511317391225845)
              ·
                refine ⟨117274873641686005427423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1250931985511317391225845 117274873641686005427423)
                ·
                  rfl

theorem cell21_1541646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_1541646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541646 prefixEnd_1541646 := by exact prefixLift 1541646
  have htrace : WordTrace (prefixWord ++ tailWord_1541646) baseStart_1541646 baseEnd_1541646 := by
    simpa [prefixWord, tailWord_1541646, baseEnd_1541646] using wordTrace_append hprefix tailTrace_1541646
  have hstable : (prefixWord ++ tailWord_1541646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541646).length < 2 ^ (prefixWord ++ tailWord_1541646).sum := by decide
  have hdescent : baseEnd_1541646 < baseStart_1541646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541674 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_1541674 : Nat := 118140960795 + 1541674 * 2 ^ 59
def prefixEnd_1541674 : Nat := 4983230072969 + 3 ^ 40 * 1541674 * 2
def baseEnd_1541674 : Nat := 351831010906536189815545

theorem tailTrace_1541674 : CollatzResearch.WordTrace tailWord_1541674 prefixEnd_1541674 351831010906536189815545 := by
  unfold tailWord_1541674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14057367554196467450542019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37486313477857246534778717 14057367554196467450542019)
  ·
    refine ⟨21086051331294701175813029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14057367554196467450542019 21086051331294701175813029)
    ·
      refine ⟨3953634624617756470464943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21086051331294701175813029 3953634624617756470464943)
      ·
        refine ⟨5930451936926634705697415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3953634624617756470464943 5930451936926634705697415)
        ·
          refine ⟨8895677905389952058546123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5930451936926634705697415 8895677905389952058546123)
          ·
            refine ⟨13343516858084928087819185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8895677905389952058546123 13343516858084928087819185)
            ·
              refine ⟨10007637643563696065864389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13343516858084928087819185 10007637643563696065864389)
              ·
                refine ⟨1876432058168193012349573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10007637643563696065864389 1876432058168193012349573)
                ·
                  refine ⟨351831010906536189815545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876432058168193012349573 351831010906536189815545)
                  ·
                    rfl

theorem cell21_1541674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_1541674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541674 prefixEnd_1541674 := by exact prefixLift 1541674
  have htrace : WordTrace (prefixWord ++ tailWord_1541674) baseStart_1541674 baseEnd_1541674 := by
    simpa [prefixWord, tailWord_1541674, baseEnd_1541674] using wordTrace_append hprefix tailTrace_1541674
  have hstable : (prefixWord ++ tailWord_1541674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541674).length < 2 ^ (prefixWord ++ tailWord_1541674).sum := by decide
  have hdescent : baseEnd_1541674 < baseStart_1541674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541688 : List Nat := [2, 1, 2, 1, 4, 3, 2, 6]
def baseStart_1541688 : Nat := 118140960795 + 1541688 * 2 ^ 59
def prefixEnd_1541688 : Nat := 4983230072969 + 3 ^ 40 * 1541688 * 2
def baseEnd_1541688 : Nat := 117278068632425092194061

theorem tailTrace_1541688 : CollatzResearch.WordTrace tailWord_1541688 prefixEnd_1541688 117278068632425092194061 := by
  unfold tailWord_1541688
  simp only [CollatzResearch.WordTrace]
  refine ⟨28114990419367575096588859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37486653892490100128785145 28114990419367575096588859)
  ·
    refine ⟨42172485629051362644883289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28114990419367575096588859 42172485629051362644883289)
    ·
      refine ⟨31629364221788521983662467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42172485629051362644883289 31629364221788521983662467)
      ·
        refine ⟨47444046332682782975493701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31629364221788521983662467 47444046332682782975493701)
        ·
          refine ⟨8895758687378021807905069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47444046332682782975493701 8895758687378021807905069)
          ·
            refine ⟨3335909507766758177964401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8895758687378021807905069 3335909507766758177964401)
            ·
              refine ⟨2501932130825068633473301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3335909507766758177964401 2501932130825068633473301)
              ·
                refine ⟨117278068632425092194061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2501932130825068633473301 117278068632425092194061)
                ·
                  rfl

theorem cell21_1541688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_1541688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541688 prefixEnd_1541688 := by exact prefixLift 1541688
  have htrace : WordTrace (prefixWord ++ tailWord_1541688) baseStart_1541688 baseEnd_1541688 := by
    simpa [prefixWord, tailWord_1541688, baseEnd_1541688] using wordTrace_append hprefix tailTrace_1541688
  have hstable : (prefixWord ++ tailWord_1541688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541688).length < 2 ^ (prefixWord ++ tailWord_1541688).sum := by decide
  have hdescent : baseEnd_1541688 < baseStart_1541688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541795 : List Nat := [1, 1, 1, 4, 1, 1, 3, 6, 3]
def baseStart_1541795 : Nat := 118140960795 + 1541795 * 2 ^ 59
def prefixEnd_1541795 : Nat := 4983230072969 + 3 ^ 40 * 1541795 * 2
def baseEnd_1541795 : Nat := 351858624755066868298631

theorem tailTrace_1541795 : CollatzResearch.WordTrace tailWord_1541795 prefixEnd_1541795 351858624755066868298631 := by
  unfold tailWord_1541795
  simp only [CollatzResearch.WordTrace]
  refine ⟨56233883449347507467322839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37489255632898338311548559 56233883449347507467322839)
  ·
    refine ⟨84350825174021261200984259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56233883449347507467322839 84350825174021261200984259)
    ·
      refine ⟨126526237761031891801476389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84350825174021261200984259 126526237761031891801476389)
      ·
        refine ⟨23723669580193479712776823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126526237761031891801476389 23723669580193479712776823)
        ·
          refine ⟨35585504370290219569165235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23723669580193479712776823 35585504370290219569165235)
          ·
            refine ⟨53378256555435329353747853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35585504370290219569165235 53378256555435329353747853)
            ·
              refine ⟨20016846208288248507655445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53378256555435329353747853 20016846208288248507655445)
              ·
                refine ⟨938289666013511648796349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20016846208288248507655445 938289666013511648796349)
                ·
                  refine ⟨351858624755066868298631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938289666013511648796349 351858624755066868298631)
                  ·
                    rfl

theorem cell21_1541795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 3].length) (baseStart_1541795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541795 prefixEnd_1541795 := by exact prefixLift 1541795
  have htrace : WordTrace (prefixWord ++ tailWord_1541795) baseStart_1541795 baseEnd_1541795 := by
    simpa [prefixWord, tailWord_1541795, baseEnd_1541795] using wordTrace_append hprefix tailTrace_1541795
  have hstable : (prefixWord ++ tailWord_1541795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541795).length < 2 ^ (prefixWord ++ tailWord_1541795).sum := by decide
  have hdescent : baseEnd_1541795 < baseStart_1541795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541823 : List Nat := [1, 1, 2, 2, 2, 3, 3, 7]
def baseStart_1541823 : Nat := 118140960795 + 1541823 * 2 ^ 59
def prefixEnd_1541823 : Nat := 4983230072969 + 3 ^ 40 * 1541823 * 2
def baseEnd_1541823 : Nat := 117288338245515013943969

theorem tailTrace_1541823 : CollatzResearch.WordTrace tailWord_1541823 prefixEnd_1541823 117288338245515013943969 := by
  unfold tailWord_1541823
  simp only [CollatzResearch.WordTrace]
  refine ⟨56234904693246068249342123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37489936462164045499561415 56234904693246068249342123)
  ·
    refine ⟨84352357039869102374013185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56234904693246068249342123 84352357039869102374013185)
    ·
      refine ⟨63264267779901826780509889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84352357039869102374013185 63264267779901826780509889)
      ·
        refine ⟨47448200834926370085382417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63264267779901826780509889 47448200834926370085382417)
        ·
          refine ⟨35586150626194777564036813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47448200834926370085382417 35586150626194777564036813)
          ·
            refine ⟨13344806484823041586513805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35586150626194777564036813 13344806484823041586513805)
            ·
              refine ⟨5004302431808640594942677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13344806484823041586513805 5004302431808640594942677)
              ·
                refine ⟨117288338245515013943969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5004302431808640594942677 117288338245515013943969)
                ·
                  rfl

theorem cell21_1541823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 7].length) (baseStart_1541823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541823 prefixEnd_1541823 := by exact prefixLift 1541823
  have htrace : WordTrace (prefixWord ++ tailWord_1541823) baseStart_1541823 baseEnd_1541823 := by
    simpa [prefixWord, tailWord_1541823, baseEnd_1541823] using wordTrace_append hprefix tailTrace_1541823
  have hstable : (prefixWord ++ tailWord_1541823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541823).length < 2 ^ (prefixWord ++ tailWord_1541823).sum := by decide
  have hdescent : baseEnd_1541823 < baseStart_1541823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541846 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1541846 : Nat := 118140960795 + 1541846 * 2 ^ 59
def prefixEnd_1541846 : Nat := 4983230072969 + 3 ^ 40 * 1541846 * 2
def baseEnd_1541846 : Nat := 351870263649902112948527

theorem tailTrace_1541846 : CollatzResearch.WordTrace tailWord_1541846 prefixEnd_1541846 351870263649902112948527 := by
  unfold tailWord_1541846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514733973260171448589337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37490495714775162118286261 3514733973260171448589337)
  ·
    refine ⟨2636050479945128586442003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3514733973260171448589337 2636050479945128586442003)
    ·
      refine ⟨3954075719917692879663005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2636050479945128586442003 3954075719917692879663005)
      ·
        refine ⟨1482778394969134829873627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3954075719917692879663005 1482778394969134829873627)
        ·
          refine ⟨2224167592453702244810441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482778394969134829873627 2224167592453702244810441)
          ·
            refine ⟨1668125694340276683607831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224167592453702244810441 1668125694340276683607831)
            ·
              refine ⟨2502188541510415025411747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668125694340276683607831 2502188541510415025411747)
              ·
                refine ⟨3753282812265622538117621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502188541510415025411747 3753282812265622538117621)
                ·
                  refine ⟨351870263649902112948527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3753282812265622538117621 351870263649902112948527)
                  ·
                    rfl

theorem cell21_1541846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1541846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541846 prefixEnd_1541846 := by exact prefixLift 1541846
  have htrace : WordTrace (prefixWord ++ tailWord_1541846) baseStart_1541846 baseEnd_1541846 := by
    simpa [prefixWord, tailWord_1541846, baseEnd_1541846] using wordTrace_append hprefix tailTrace_1541846
  have hstable : (prefixWord ++ tailWord_1541846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541846).length < 2 ^ (prefixWord ++ tailWord_1541846).sum := by decide
  have hdescent : baseEnd_1541846 < baseStart_1541846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541908 : List Nat := [2, 4, 4, 1, 2, 1, 1, 6]
def baseStart_1541908 : Nat := 118140960795 + 1541908 * 2 ^ 59
def prefixEnd_1541908 : Nat := 4983230072969 + 3 ^ 40 * 1541908 * 2
def baseEnd_1541908 : Nat := 117294804298201260971689

theorem tailTrace_1541908 : CollatzResearch.WordTrace tailWord_1541908 prefixEnd_1541908 117294804298201260971689 := by
  unfold tailWord_1541908
  simp only [CollatzResearch.WordTrace]
  refine ⟨28119002448969063883093189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37492003265292085177457585 28119002448969063883093189)
  ·
    refine ⟨5272312959181699478079973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28119002448969063883093189 5272312959181699478079973)
    ·
      refine ⟨988558679846568652139995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5272312959181699478079973 988558679846568652139995)
      ·
        refine ⟨1482838019769852978209993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988558679846568652139995 1482838019769852978209993)
        ·
          refine ⟨1112128514827389733657495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1482838019769852978209993 1112128514827389733657495)
          ·
            refine ⟨1668192772241084600486243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112128514827389733657495 1668192772241084600486243)
            ·
              refine ⟨2502289158361626900729365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668192772241084600486243 2502289158361626900729365)
              ·
                refine ⟨117294804298201260971689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2502289158361626900729365 117294804298201260971689)
                ·
                  rfl

theorem cell21_1541908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 6].length) (baseStart_1541908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541908 prefixEnd_1541908 := by exact prefixLift 1541908
  have htrace : WordTrace (prefixWord ++ tailWord_1541908) baseStart_1541908 baseEnd_1541908 := by
    simpa [prefixWord, tailWord_1541908, baseEnd_1541908] using wordTrace_append hprefix tailTrace_1541908
  have hstable : (prefixWord ++ tailWord_1541908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541908).length < 2 ^ (prefixWord ++ tailWord_1541908).sum := by decide
  have hdescent : baseEnd_1541908 < baseStart_1541908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541978 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_1541978 : Nat := 118140960795 + 1541978 * 2 ^ 59
def prefixEnd_1541978 : Nat := 4983230072969 + 3 ^ 40 * 1541978 * 2
def baseEnd_1541978 : Nat := 351900387848299216748257

theorem tailTrace_1541978 : CollatzResearch.WordTrace tailWord_1541978 prefixEnd_1541978 351900387848299216748257 := by
  unfold tailWord_1541978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14060139501921132430308647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37493705338456353147489725 14060139501921132430308647)
  ·
    refine ⟨21090209252881698645462971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14060139501921132430308647 21090209252881698645462971)
    ·
      refine ⟨31635313879322547968194457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21090209252881698645462971 31635313879322547968194457)
      ·
        refine ⟨23726485409491910976145843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31635313879322547968194457 23726485409491910976145843)
        ·
          refine ⟨35589728114237866464218765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23726485409491910976145843 35589728114237866464218765)
          ·
            refine ⟨13346148042839199924082037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35589728114237866464218765 13346148042839199924082037)
            ·
              refine ⟨1251201379016174992882691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13346148042839199924082037 1251201379016174992882691)
              ·
                refine ⟨1876802068524262489324037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251201379016174992882691 1876802068524262489324037)
                ·
                  refine ⟨351900387848299216748257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876802068524262489324037 351900387848299216748257)
                  ·
                    rfl

theorem cell21_1541978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_1541978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1541978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1541978 prefixEnd_1541978 := by exact prefixLift 1541978
  have htrace : WordTrace (prefixWord ++ tailWord_1541978) baseStart_1541978 baseEnd_1541978 := by
    simpa [prefixWord, tailWord_1541978, baseEnd_1541978] using wordTrace_append hprefix tailTrace_1541978
  have hstable : (prefixWord ++ tailWord_1541978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541978).length < 2 ^ (prefixWord ++ tailWord_1541978).sum := by decide
  have hdescent : baseEnd_1541978 < baseStart_1541978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542037 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 4]
def baseStart_1542037 : Nat := 118140960795 + 1542037 * 2 ^ 59
def prefixEnd_1542037 : Nat := 4983230072969 + 3 ^ 40 * 1542037 * 2
def baseEnd_1542037 : Nat := 351913852452128225264803

theorem tailTrace_1542037 : CollatzResearch.WordTrace tailWord_1542037 prefixEnd_1542037 351913852452128225264803 := by
  unfold tailWord_1542037
  simp only [CollatzResearch.WordTrace]
  refine ⟨56242709914470782797632365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37495139942980521865088243 56242709914470782797632365)
  ·
    refine ⟨21091016217926543549112137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56242709914470782797632365 21091016217926543549112137)
    ·
      refine ⟨15818262163444907661834103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21091016217926543549112137 15818262163444907661834103)
      ·
        refine ⟨23727393245167361492751155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15818262163444907661834103 23727393245167361492751155)
        ·
          refine ⟨35591089867751042239126733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23727393245167361492751155 35591089867751042239126733)
          ·
            refine ⟨13346658700406640839672525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35591089867751042239126733 13346658700406640839672525)
            ·
              refine ⟨5004997012652490314877197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13346658700406640839672525 5004997012652490314877197)
              ·
                refine ⟨1876873879744683868078949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5004997012652490314877197 1876873879744683868078949)
                ·
                  refine ⟨351913852452128225264803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876873879744683868078949 351913852452128225264803)
                  ·
                    rfl

theorem cell21_1542037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_1542037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542037 prefixEnd_1542037 := by exact prefixLift 1542037
  have htrace : WordTrace (prefixWord ++ tailWord_1542037) baseStart_1542037 baseEnd_1542037 := by
    simpa [prefixWord, tailWord_1542037, baseEnd_1542037] using wordTrace_append hprefix tailTrace_1542037
  have hstable : (prefixWord ++ tailWord_1542037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542037).length < 2 ^ (prefixWord ++ tailWord_1542037).sum := by decide
  have hdescent : baseEnd_1542037 < baseStart_1542037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542068 : List Nat := [2, 5, 2, 1, 11]
def baseStart_1542068 : Nat := 118140960795 + 1542068 * 2 ^ 59
def prefixEnd_1542068 : Nat := 4983230072969 + 3 ^ 40 * 1542068 * 2
def baseEnd_1542068 : Nat := 4344702803388630373433

theorem tailTrace_1542068 : CollatzResearch.WordTrace tailWord_1542068 prefixEnd_1542068 4344702803388630373433 := by
  unfold tailWord_1542068
  simp only [CollatzResearch.WordTrace]
  refine ⟨28121920288679237546005429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37495893718238983394673905 28121920288679237546005429)
  ·
    refine ⟨2636430027063678519938009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28121920288679237546005429 2636430027063678519938009)
    ·
      refine ⟨1977322520297758889953507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2636430027063678519938009 1977322520297758889953507)
      ·
        refine ⟨2965983780446638334930261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977322520297758889953507 2965983780446638334930261)
        ·
          refine ⟨4344702803388630373433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2965983780446638334930261 4344702803388630373433)
          ·
            rfl

theorem cell21_1542068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 11].length) (baseStart_1542068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542068 prefixEnd_1542068 := by exact prefixLift 1542068
  have htrace : WordTrace (prefixWord ++ tailWord_1542068) baseStart_1542068 baseEnd_1542068 := by
    simpa [prefixWord, tailWord_1542068, baseEnd_1542068] using wordTrace_append hprefix tailTrace_1542068
  have hstable : (prefixWord ++ tailWord_1542068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542068).length < 2 ^ (prefixWord ++ tailWord_1542068).sum := by decide
  have hdescent : baseEnd_1542068 < baseStart_1542068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542102 : List Nat := [5, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1542102 : Nat := 118140960795 + 1542102 * 2 ^ 59
def prefixEnd_1542102 : Nat := 4983230072969 + 3 ^ 40 * 1542102 * 2
def baseEnd_1542102 : Nat := 117309562112567518893779

theorem tailTrace_1542102 : CollatzResearch.WordTrace tailWord_1542102 prefixEnd_1542102 117309562112567518893779 := by
  unfold tailWord_1542102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515317541202206181171785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37496720439490199265832373 3515317541202206181171785)
  ·
    refine ⟨2636488155901654635878839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3515317541202206181171785 2636488155901654635878839)
    ·
      refine ⟨3954732233852481953818259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2636488155901654635878839 3954732233852481953818259)
      ·
        refine ⟨5932098350778722930727389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3954732233852481953818259 5932098350778722930727389)
        ·
          refine ⟨2224536881542021099022771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5932098350778722930727389 2224536881542021099022771)
          ·
            refine ⟨3336805322313031648534157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224536881542021099022771 3336805322313031648534157)
            ·
              refine ⟨1251301995867386868200309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3336805322313031648534157 1251301995867386868200309)
              ·
                refine ⟨117309562112567518893779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1251301995867386868200309 117309562112567518893779)
                ·
                  rfl

theorem cell21_1542102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1542102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542102 prefixEnd_1542102 := by exact prefixLift 1542102
  have htrace : WordTrace (prefixWord ++ tailWord_1542102) baseStart_1542102 baseEnd_1542102 := by
    simpa [prefixWord, tailWord_1542102, baseEnd_1542102] using wordTrace_append hprefix tailTrace_1542102
  have hstable : (prefixWord ++ tailWord_1542102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542102).length < 2 ^ (prefixWord ++ tailWord_1542102).sum := by decide
  have hdescent : baseEnd_1542102 < baseStart_1542102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542158 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_1542158 : Nat := 118140960795 + 1542158 * 2 ^ 59
def prefixEnd_1542158 : Nat := 4983230072969 + 3 ^ 40 * 1542158 * 2
def baseEnd_1542158 : Nat := 351941466300658903747889

theorem tailTrace_1542158 : CollatzResearch.WordTrace tailWord_1542158 prefixEnd_1542158 351941466300658903747889 := by
  unfold tailWord_1542158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7030890393379052557848391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37498082098021613641858085 7030890393379052557848391)
  ·
    refine ⟨10546335590068578836772587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7030890393379052557848391 10546335590068578836772587)
    ·
      refine ⟨15819503385102868255158881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10546335590068578836772587 15819503385102868255158881)
      ·
        refine ⟨11864627538827151191369161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15819503385102868255158881 11864627538827151191369161)
        ·
          refine ⟨8898470654120363393526871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11864627538827151191369161 8898470654120363393526871)
          ·
            refine ⟨13347705981180545090290307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8898470654120363393526871 13347705981180545090290307)
            ·
              refine ⟨20021558971770817635435461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13347705981180545090290307 20021558971770817635435461)
              ·
                refine ⟨3754042307207028306644149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20021558971770817635435461 3754042307207028306644149)
                ·
                  refine ⟨351941466300658903747889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3754042307207028306644149 351941466300658903747889)
                  ·
                    rfl

theorem cell21_1542158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_1542158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542158 prefixEnd_1542158 := by exact prefixLift 1542158
  have htrace : WordTrace (prefixWord ++ tailWord_1542158) baseStart_1542158 baseEnd_1542158 := by
    simpa [prefixWord, tailWord_1542158, baseEnd_1542158] using wordTrace_append hprefix tailTrace_1542158
  have hstable : (prefixWord ++ tailWord_1542158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542158).length < 2 ^ (prefixWord ++ tailWord_1542158).sum := by decide
  have hdescent : baseEnd_1542158 < baseStart_1542158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542192 : List Nat := [2, 1, 1, 1, 2, 6, 3, 2, 3]
def baseStart_1542192 : Nat := 118140960795 + 1542192 * 2 ^ 59
def prefixEnd_1542192 : Nat := 4983230072969 + 3 ^ 40 * 1542192 * 2
def baseEnd_1542192 : Nat := 351949225563882400181153

theorem tailTrace_1542192 : CollatzResearch.WordTrace tailWord_1542192 prefixEnd_1542192 351949225563882400181153 := by
  unfold tailWord_1542192
  simp only [CollatzResearch.WordTrace]
  refine ⟨28124181614454622134762415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37498908819272829513016553 28124181614454622134762415)
  ·
    refine ⟨42186272421681933202143623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28124181614454622134762415 42186272421681933202143623)
    ·
      refine ⟨63279408632522899803215435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42186272421681933202143623 63279408632522899803215435)
      ·
        refine ⟨94919112948784349704823153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63279408632522899803215435 94919112948784349704823153)
        ·
          refine ⟨71189334711588262278617365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94919112948784349704823153 71189334711588262278617365)
          ·
            refine ⟨3337000064605699794310189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71189334711588262278617365 3337000064605699794310189)
            ·
              refine ⟨1251375024227137422866321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3337000064605699794310189 1251375024227137422866321)
              ·
                refine ⟨938531268170353067149741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251375024227137422866321 938531268170353067149741)
                ·
                  refine ⟨351949225563882400181153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938531268170353067149741 351949225563882400181153)
                  ·
                    rfl

theorem cell21_1542192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 3].length) (baseStart_1542192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542192 prefixEnd_1542192 := by exact prefixLift 1542192
  have htrace : WordTrace (prefixWord ++ tailWord_1542192) baseStart_1542192 baseEnd_1542192 := by
    simpa [prefixWord, tailWord_1542192, baseEnd_1542192] using wordTrace_append hprefix tailTrace_1542192
  have hstable : (prefixWord ++ tailWord_1542192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542192).length < 2 ^ (prefixWord ++ tailWord_1542192).sum := by decide
  have hdescent : baseEnd_1542192 < baseStart_1542192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542217 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 7]
def baseStart_1542217 : Nat := 118140960795 + 1542217 * 2 ^ 59
def prefixEnd_1542217 : Nat := 4983230072969 + 3 ^ 40 * 1542217 * 2
def baseEnd_1542217 : Nat := 351954930904487912264435

theorem tailTrace_1542217 : CollatzResearch.WordTrace tailWord_1542217 prefixEnd_1542217 351954930904487912264435 := by
  unfold tailWord_1542217
  simp only [CollatzResearch.WordTrace]
  refine ⟨56249275053818673539184905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37499516702545782359456603 56249275053818673539184905)
  ·
    refine ⟨42186956290364005154388679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56249275053818673539184905 42186956290364005154388679)
    ·
      refine ⟨63280434435546007731583019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42186956290364005154388679 63280434435546007731583019)
      ·
        refine ⟨94920651653319011597374529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63280434435546007731583019 94920651653319011597374529)
        ·
          refine ⟨71190488739989258698030897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94920651653319011597374529 71190488739989258698030897)
          ·
            refine ⟨53392866554991944023523173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71190488739989258698030897 53392866554991944023523173)
            ·
              refine ⟨10011162479060989504410595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53392866554991944023523173 10011162479060989504410595)
              ·
                refine ⟨15016743718591484256615893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10011162479060989504410595 15016743718591484256615893)
                ·
                  refine ⟨351954930904487912264435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15016743718591484256615893 351954930904487912264435)
                  ·
                    rfl

theorem cell21_1542217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_1542217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542217 prefixEnd_1542217 := by exact prefixLift 1542217
  have htrace : WordTrace (prefixWord ++ tailWord_1542217) baseStart_1542217 baseEnd_1542217 := by
    simpa [prefixWord, tailWord_1542217, baseEnd_1542217] using wordTrace_append hprefix tailTrace_1542217
  have hstable : (prefixWord ++ tailWord_1542217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542217).length < 2 ^ (prefixWord ++ tailWord_1542217).sum := by decide
  have hdescent : baseEnd_1542217 < baseStart_1542217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542265 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 4]
def baseStart_1542265 : Nat := 118140960795 + 1542265 * 2 ^ 59
def prefixEnd_1542265 : Nat := 4983230072969 + 3 ^ 40 * 1542265 * 2
def baseEnd_1542265 : Nat := 351965885158450495464337

theorem tailTrace_1542265 : CollatzResearch.WordTrace tailWord_1542265 prefixEnd_1542265 351965885158450495464337 := by
  unfold tailWord_1542265
  simp only [CollatzResearch.WordTrace]
  refine ⟨56251025757644777736932249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37500683838429851824621499 56251025757644777736932249)
  ·
    refine ⟨42188269318233583302699187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56251025757644777736932249 42188269318233583302699187)
    ·
      refine ⟨63282403977350374954048781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42188269318233583302699187 63282403977350374954048781)
      ·
        refine ⟨23730901491506390607768293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63282403977350374954048781 23730901491506390607768293)
        ·
          refine ⟨4449544029657448238956555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23730901491506390607768293 4449544029657448238956555)
          ·
            refine ⟨6674316044486172358434833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449544029657448238956555 6674316044486172358434833)
            ·
              refine ⟨5005737033364629268826125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6674316044486172358434833 5005737033364629268826125)
              ·
                refine ⟨1877151387511735975809797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5005737033364629268826125 1877151387511735975809797)
                ·
                  refine ⟨351965885158450495464337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877151387511735975809797 351965885158450495464337)
                  ·
                    rfl

theorem cell21_1542265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_1542265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542265 prefixEnd_1542265 := by exact prefixLift 1542265
  have htrace : WordTrace (prefixWord ++ tailWord_1542265) baseStart_1542265 baseEnd_1542265 := by
    simpa [prefixWord, tailWord_1542265, baseEnd_1542265] using wordTrace_append hprefix tailTrace_1542265
  have hstable : (prefixWord ++ tailWord_1542265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542265).length < 2 ^ (prefixWord ++ tailWord_1542265).sum := by decide
  have hdescent : baseEnd_1542265 < baseStart_1542265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542293 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 7]
def baseStart_1542293 : Nat := 118140960795 + 1542293 * 2 ^ 59
def prefixEnd_1542293 : Nat := 4983230072969 + 3 ^ 40 * 1542293 * 2
def baseEnd_1542293 : Nat := 351972275139928668997613

theorem tailTrace_1542293 : CollatzResearch.WordTrace tailWord_1542293 prefixEnd_1542293 351972275139928668997613 := by
  unfold tailWord_1542293
  simp only [CollatzResearch.WordTrace]
  refine ⟨56252047001543338518951533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37501364667695559012634355 56252047001543338518951533)
  ·
    refine ⟨21094517625578751944606825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56252047001543338518951533 21094517625578751944606825)
    ·
      refine ⟨15820888219184063958455119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21094517625578751944606825 15820888219184063958455119)
      ·
        refine ⟨23731332328776095937682679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15820888219184063958455119 23731332328776095937682679)
        ·
          refine ⟨35596998493164143906524019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23731332328776095937682679 35596998493164143906524019)
          ·
            refine ⟨53395497739746215859786029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35596998493164143906524019 53395497739746215859786029)
            ·
              refine ⟨20023311652404830947419761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53395497739746215859786029 20023311652404830947419761)
              ·
                refine ⟨15017483739303623210564821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20023311652404830947419761 15017483739303623210564821)
                ·
                  refine ⟨351972275139928668997613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15017483739303623210564821 351972275139928668997613)
                  ·
                    rfl

theorem cell21_1542293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_1542293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542293 prefixEnd_1542293 := by exact prefixLift 1542293
  have htrace : WordTrace (prefixWord ++ tailWord_1542293) baseStart_1542293 baseEnd_1542293 := by
    simpa [prefixWord, tailWord_1542293, baseEnd_1542293] using wordTrace_append hprefix tailTrace_1542293
  have hstable : (prefixWord ++ tailWord_1542293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542293).length < 2 ^ (prefixWord ++ tailWord_1542293).sum := by decide
  have hdescent : baseEnd_1542293 < baseStart_1542293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542358 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1542358 : Nat := 118140960795 + 1542358 * 2 ^ 59
def prefixEnd_1542358 : Nat := 4983230072969 + 3 ^ 40 * 1542358 * 2
def baseEnd_1542358 : Nat := 351987109025503000414147

theorem tailTrace_1542358 : CollatzResearch.WordTrace tailWord_1542358 prefixEnd_1542358 351987109025503000414147 := by
  unfold tailWord_1542358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515901109144240913754233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37502945164205236413378485 3515901109144240913754233)
  ·
    refine ⟨2636925831858180685315675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3515901109144240913754233 2636925831858180685315675)
    ·
      refine ⟨3955388747787271027973513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2636925831858180685315675 3955388747787271027973513)
      ·
        refine ⟨2966541560840453270980135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3955388747787271027973513 2966541560840453270980135)
        ·
          refine ⟨4449812341260679906470203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966541560840453270980135 4449812341260679906470203)
          ·
            refine ⟨6674718511891019859705305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449812341260679906470203 6674718511891019859705305)
            ·
              refine ⟨5006038883918264894778979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6674718511891019859705305 5006038883918264894778979)
              ·
                refine ⟨7509058325877397342168469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5006038883918264894778979 7509058325877397342168469)
                ·
                  refine ⟨351987109025503000414147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7509058325877397342168469 351987109025503000414147)
                  ·
                    rfl

theorem cell21_1542358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1542358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542358 prefixEnd_1542358 := by exact prefixLift 1542358
  have htrace : WordTrace (prefixWord ++ tailWord_1542358) baseStart_1542358 baseEnd_1542358 := by
    simpa [prefixWord, tailWord_1542358, baseEnd_1542358] using wordTrace_append hprefix tailTrace_1542358
  have hstable : (prefixWord ++ tailWord_1542358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542358).length < 2 ^ (prefixWord ++ tailWord_1542358).sum := by decide
  have hdescent : baseEnd_1542358 < baseStart_1542358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542375 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 4]
def baseStart_1542375 : Nat := 118140960795 + 1542375 * 2 ^ 59
def prefixEnd_1542375 : Nat := 4983230072969 + 3 ^ 40 * 1542375 * 2
def baseEnd_1542375 : Nat := 351990988657114748630779

theorem tailTrace_1542375 : CollatzResearch.WordTrace tailWord_1542375 prefixEnd_1542375 351990988657114748630779 := by
  unfold tailWord_1542375
  simp only [CollatzResearch.WordTrace]
  refine ⟨56255037787246266523436579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37503358524830844348957719 56255037787246266523436579)
  ·
    refine ⟨84382556680869399785154869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56255037787246266523436579 84382556680869399785154869)
    ·
      refine ⟨7910864688831506229858269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84382556680869399785154869 7910864688831506229858269)
      ·
        refine ⟨2966574258311814836196851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7910864688831506229858269 2966574258311814836196851)
        ·
          refine ⟨4449861387467722254295277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966574258311814836196851 4449861387467722254295277)
          ·
            refine ⟨1668698020300395845360729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4449861387467722254295277 1668698020300395845360729)
            ·
              refine ⟨1251523515225296884020547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668698020300395845360729 1251523515225296884020547)
              ·
                refine ⟨1877285272837945326030821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251523515225296884020547 1877285272837945326030821)
                ·
                  refine ⟨351990988657114748630779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877285272837945326030821 351990988657114748630779)
                  ·
                    rfl

theorem cell21_1542375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 4].length) (baseStart_1542375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542375 prefixEnd_1542375 := by exact prefixLift 1542375
  have htrace : WordTrace (prefixWord ++ tailWord_1542375) baseStart_1542375 baseEnd_1542375 := by
    simpa [prefixWord, tailWord_1542375, baseEnd_1542375] using wordTrace_append hprefix tailTrace_1542375
  have hstable : (prefixWord ++ tailWord_1542375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542375).length < 2 ^ (prefixWord ++ tailWord_1542375).sum := by decide
  have hdescent : baseEnd_1542375 < baseStart_1542375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542417 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 4]
def baseStart_1542417 : Nat := 118140960795 + 1542417 * 2 ^ 59
def prefixEnd_1542417 : Nat := 4983230072969 + 3 ^ 40 * 1542417 * 2
def baseEnd_1542417 : Nat := 352000573629332008930693

theorem tailTrace_1542417 : CollatzResearch.WordTrace tailWord_1542417 prefixEnd_1542417 352000573629332008930693 := by
  unfold tailWord_1542417
  simp only [CollatzResearch.WordTrace]
  refine ⟨56256569653094107696465505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37504379768729405130977003 56256569653094107696465505)
  ·
    refine ⟨42192427239820580772349129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56256569653094107696465505 42192427239820580772349129)
    ·
      refine ⟨31644320429865435579261847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42192427239820580772349129 31644320429865435579261847)
      ·
        refine ⟨47466480644798153368892771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31644320429865435579261847 47466480644798153368892771)
        ·
          refine ⟨71199720967197230053339157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47466480644798153368892771 71199720967197230053339157)
          ·
            refine ⟨3337486920337370158750273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71199720967197230053339157 3337486920337370158750273)
            ·
              refine ⟨2503115190253027619062705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337486920337370158750273 2503115190253027619062705)
              ·
                refine ⟨1877336392689770714297029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503115190253027619062705 1877336392689770714297029)
                ·
                  refine ⟨352000573629332008930693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877336392689770714297029 352000573629332008930693)
                  ·
                    rfl

theorem cell21_1542417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_1542417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542417 prefixEnd_1542417 := by exact prefixLift 1542417
  have htrace : WordTrace (prefixWord ++ tailWord_1542417) baseStart_1542417 baseEnd_1542417 := by
    simpa [prefixWord, tailWord_1542417, baseEnd_1542417] using wordTrace_append hprefix tailTrace_1542417
  have hstable : (prefixWord ++ tailWord_1542417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542417).length < 2 ^ (prefixWord ++ tailWord_1542417).sum := by decide
  have hdescent : baseEnd_1542417 < baseStart_1542417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542431 : List Nat := [1, 1, 2, 4, 3, 1, 3, 6]
def baseStart_1542431 : Nat := 118140960795 + 1542431 * 2 ^ 59
def prefixEnd_1542431 : Nat := 4983230072969 + 3 ^ 40 * 1542431 * 2
def baseEnd_1542431 : Nat := 117334589540023698565777

theorem tailTrace_1542431 : CollatzResearch.WordTrace tailWord_1542431 prefixEnd_1542431 117334589540023698565777 := by
  unfold tailWord_1542431
  simp only [CollatzResearch.WordTrace]
  refine ⟨56257080275043388087475147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37504720183362258724983431 56257080275043388087475147)
  ·
    refine ⟨84385620412565082131212721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56257080275043388087475147 84385620412565082131212721)
    ·
      refine ⟨63289215309423811598409541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84385620412565082131212721 63289215309423811598409541)
      ·
        refine ⟨11866727870516964674701789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63289215309423811598409541 11866727870516964674701789)
        ·
          refine ⟨4450022951443861753013171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11866727870516964674701789 4450022951443861753013171)
          ·
            refine ⟨6675034427165792629519757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4450022951443861753013171 6675034427165792629519757)
            ·
              refine ⟨2503137910187172236069909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6675034427165792629519757 2503137910187172236069909)
              ·
                refine ⟨117334589540023698565777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2503137910187172236069909 117334589540023698565777)
                ·
                  rfl

theorem cell21_1542431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 6].length) (baseStart_1542431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542431 prefixEnd_1542431 := by exact prefixLift 1542431
  have htrace : WordTrace (prefixWord ++ tailWord_1542431) baseStart_1542431 baseEnd_1542431 := by
    simpa [prefixWord, tailWord_1542431, baseEnd_1542431] using wordTrace_append hprefix tailTrace_1542431
  have hstable : (prefixWord ++ tailWord_1542431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542431).length < 2 ^ (prefixWord ++ tailWord_1542431).sum := by decide
  have hdescent : baseEnd_1542431 < baseStart_1542431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542468 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 4]
def baseStart_1542468 : Nat := 118140960795 + 1542468 * 2 ^ 59
def prefixEnd_1542468 : Nat := 4983230072969 + 3 ^ 40 * 1542468 * 2
def baseEnd_1542468 : Nat := 352012212524167253580589

theorem tailTrace_1542468 : CollatzResearch.WordTrace tailWord_1542468 prefixEnd_1542468 352012212524167253580589 := by
  unfold tailWord_1542468
  simp only [CollatzResearch.WordTrace]
  refine ⟨28129214887954671703286029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37505619850606228937714705 28129214887954671703286029)
  ·
    refine ⟨10548455582983001888732261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28129214887954671703286029 10548455582983001888732261)
    ·
      refine ⟨1977835421809312854137299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10548455582983001888732261 1977835421809312854137299)
      ·
        refine ⟨2966753132713969281205949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977835421809312854137299 2966753132713969281205949)
        ·
          refine ⟨1112532424767738480452231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2966753132713969281205949 1112532424767738480452231)
          ·
            refine ⟨1668798637151607720678347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112532424767738480452231 1668798637151607720678347)
            ·
              refine ⟨2503197955727411581017521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668798637151607720678347 2503197955727411581017521)
              ·
                refine ⟨1877398466795558685763141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503197955727411581017521 1877398466795558685763141)
                ·
                  refine ⟨352012212524167253580589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877398466795558685763141 352012212524167253580589)
                  ·
                    rfl

theorem cell21_1542468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_1542468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542468 prefixEnd_1542468 := by exact prefixLift 1542468
  have htrace : WordTrace (prefixWord ++ tailWord_1542468) baseStart_1542468 baseEnd_1542468 := by
    simpa [prefixWord, tailWord_1542468, baseEnd_1542468] using wordTrace_append hprefix tailTrace_1542468
  have hstable : (prefixWord ++ tailWord_1542468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542468).length < 2 ^ (prefixWord ++ tailWord_1542468).sum := by decide
  have hdescent : baseEnd_1542468 < baseStart_1542468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542476 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_1542476 : Nat := 118140960795 + 1542476 * 2 ^ 59
def prefixEnd_1542476 : Nat := 4983230072969 + 3 ^ 40 * 1542476 * 2
def baseEnd_1542476 : Nat := 352014038233161017447239

theorem tailTrace_1542476 : CollatzResearch.WordTrace tailWord_1542476 prefixEnd_1542476 352014038233161017447239 := by
  unfold tailWord_1542476
  simp only [CollatzResearch.WordTrace]
  refine ⟨28129360779940180386431641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37505814373253573848575521 28129360779940180386431641)
  ·
    refine ⟨21097020584955135289823731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28129360779940180386431641 21097020584955135289823731)
    ·
      refine ⟨31645530877432702934735597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21097020584955135289823731 31645530877432702934735597)
      ·
        refine ⟨11867074079037263600525849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31645530877432702934735597 11867074079037263600525849)
        ·
          refine ⟨8900305559277947700394387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11867074079037263600525849 8900305559277947700394387)
          ·
            refine ⟨13350458338916921550591581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8900305559277947700394387 13350458338916921550591581)
            ·
              refine ⟨5006421877093845581471843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13350458338916921550591581 5006421877093845581471843)
              ·
                refine ⟨7509632815640768372207765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5006421877093845581471843 7509632815640768372207765)
                ·
                  refine ⟨352014038233161017447239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7509632815640768372207765 352014038233161017447239)
                  ·
                    rfl

theorem cell21_1542476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_1542476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542476 prefixEnd_1542476 := by exact prefixLift 1542476
  have htrace : WordTrace (prefixWord ++ tailWord_1542476) baseStart_1542476 baseEnd_1542476 := by
    simpa [prefixWord, tailWord_1542476, baseEnd_1542476] using wordTrace_append hprefix tailTrace_1542476
  have hstable : (prefixWord ++ tailWord_1542476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542476).length < 2 ^ (prefixWord ++ tailWord_1542476).sum := by decide
  have hdescent : baseEnd_1542476 < baseStart_1542476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542490 : List Nat := [3, 1, 1, 2, 1, 2, 1, 10]
def baseStart_1542490 : Nat := 118140960795 + 1542490 * 2 ^ 59
def prefixEnd_1542490 : Nat := 4983230072969 + 3 ^ 40 * 1542490 * 2
def baseEnd_1542490 : Nat := 117339077741300034737959

theorem tailTrace_1542490 : CollatzResearch.WordTrace tailWord_1542490 prefixEnd_1542490 117339077741300034737959 := by
  unfold tailWord_1542490
  simp only [CollatzResearch.WordTrace]
  refine ⟨14064808045457410290968231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37506154787886427442581949 14064808045457410290968231)
  ·
    refine ⟨21097212068186115436452347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14064808045457410290968231 21097212068186115436452347)
    ·
      refine ⟨31645818102279173154678521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21097212068186115436452347 31645818102279173154678521)
      ·
        refine ⟨23734363576709379866008891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31645818102279173154678521 23734363576709379866008891)
        ·
          refine ⟨35601545365064069799013337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23734363576709379866008891 35601545365064069799013337)
          ·
            refine ⟨26701159023798052349260003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35601545365064069799013337 26701159023798052349260003)
            ·
              refine ⟨40051738535697078523890005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26701159023798052349260003 40051738535697078523890005)
              ·
                refine ⟨117339077741300034737959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40051738535697078523890005 117339077741300034737959)
                ·
                  rfl

theorem cell21_1542490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_1542490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542490 prefixEnd_1542490 := by exact prefixLift 1542490
  have htrace : WordTrace (prefixWord ++ tailWord_1542490) baseStart_1542490 baseEnd_1542490 := by
    simpa [prefixWord, tailWord_1542490, baseEnd_1542490] using wordTrace_append hprefix tailTrace_1542490
  have hstable : (prefixWord ++ tailWord_1542490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542490).length < 2 ^ (prefixWord ++ tailWord_1542490).sum := by decide
  have hdescent : baseEnd_1542490 < baseStart_1542490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542530 : List Nat := [3, 4, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1542530 : Nat := 118140960795 + 1542530 * 2 ^ 59
def prefixEnd_1542530 : Nat := 4983230072969 + 3 ^ 40 * 1542530 * 2
def baseEnd_1542530 : Nat := 352026361768868923547129

theorem tailTrace_1542530 : CollatzResearch.WordTrace tailWord_1542530 prefixEnd_1542530 352026361768868923547129 := by
  unfold tailWord_1542530
  simp only [CollatzResearch.WordTrace]
  refine ⟨14065172775421181998832261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37507127401123151996886029 14065172775421181998832261)
  ·
    refine ⟨2637219895391471624781049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14065172775421181998832261 2637219895391471624781049)
    ·
      refine ⟨1977914921543603718585787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2637219895391471624781049 1977914921543603718585787)
      ·
        refine ⟨2966872382315405577878681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977914921543603718585787 2966872382315405577878681)
        ·
          refine ⟨2225154286736554183409011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2966872382315405577878681 2225154286736554183409011)
          ·
            refine ⟨3337731430104831275113517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225154286736554183409011 3337731430104831275113517)
            ·
              refine ⟨1251649286289311728167569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3337731430104831275113517 1251649286289311728167569)
              ·
                refine ⟨938736964716983796125677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251649286289311728167569 938736964716983796125677)
                ·
                  refine ⟨352026361768868923547129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938736964716983796125677 352026361768868923547129)
                  ·
                    rfl

theorem cell21_1542530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1542530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542530 prefixEnd_1542530 := by exact prefixLift 1542530
  have htrace : WordTrace (prefixWord ++ tailWord_1542530) baseStart_1542530 baseEnd_1542530 := by
    simpa [prefixWord, tailWord_1542530, baseEnd_1542530] using wordTrace_append hprefix tailTrace_1542530
  have hstable : (prefixWord ++ tailWord_1542530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542530).length < 2 ^ (prefixWord ++ tailWord_1542530).sum := by decide
  have hdescent : baseEnd_1542530 < baseStart_1542530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542631 : List Nat := [1, 1, 5, 2, 1, 1, 4, 3, 3]
def baseStart_1542631 : Nat := 118140960795 + 1542631 * 2 ^ 59
def prefixEnd_1542631 : Nat := 4983230072969 + 3 ^ 40 * 1542631 * 2
def baseEnd_1542631 : Nat := 352049411344915192363589

theorem tailTrace_1542631 : CollatzResearch.WordTrace tailWord_1542631 prefixEnd_1542631 352049411344915192363589 := by
  unfold tailWord_1542631
  simp only [CollatzResearch.WordTrace]
  refine ⟨56264374874318822244755747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37509583249545881496503831 56264374874318822244755747)
  ·
    refine ⟨84396562311478233367133621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56264374874318822244755747 84396562311478233367133621)
    ·
      refine ⟨7912177716701084378168777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84396562311478233367133621 7912177716701084378168777)
      ·
        refine ⟨5934133287525813283626583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7912177716701084378168777 5934133287525813283626583)
        ·
          refine ⟨8901199931288719925439875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5934133287525813283626583 8901199931288719925439875)
          ·
            refine ⟨13351799896933079888159813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901199931288719925439875 13351799896933079888159813)
            ·
              refine ⟨2503462480674952479029965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13351799896933079888159813 2503462480674952479029965)
              ·
                refine ⟨938798430253107179636237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2503462480674952479029965 938798430253107179636237)
                ·
                  refine ⟨352049411344915192363589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938798430253107179636237 352049411344915192363589)
                  ·
                    rfl

theorem cell21_1542631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 3].length) (baseStart_1542631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542631 prefixEnd_1542631 := by exact prefixLift 1542631
  have htrace : WordTrace (prefixWord ++ tailWord_1542631) baseStart_1542631 baseEnd_1542631 := by
    simpa [prefixWord, tailWord_1542631, baseEnd_1542631] using wordTrace_append hprefix tailTrace_1542631
  have hstable : (prefixWord ++ tailWord_1542631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542631).length < 2 ^ (prefixWord ++ tailWord_1542631).sum := by decide
  have hdescent : baseEnd_1542631 < baseStart_1542631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542676 : List Nat := [2, 4, 3, 1, 1, 2, 1, 7]
def baseStart_1542676 : Nat := 118140960795 + 1542676 * 2 ^ 59
def prefixEnd_1542676 : Nat := 4983230072969 + 3 ^ 40 * 1542676 * 2
def baseEnd_1542676 : Nat := 117353226986001704704499

theorem tailTrace_1542676 : CollatzResearch.WordTrace tailWord_1542676 prefixEnd_1542676 117353226986001704704499 := by
  unfold tailWord_1542676
  simp only [CollatzResearch.WordTrace]
  refine ⟨28133008079577897465071941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37510677439437196620095921 28133008079577897465071941)
  ·
    refine ⟨5274939014920855774700989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28133008079577897465071941 5274939014920855774700989)
    ·
      refine ⟨1978102130595320915512871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5274939014920855774700989 1978102130595320915512871)
      ·
        refine ⟨2967153195892981373269307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978102130595320915512871 2967153195892981373269307)
        ·
          refine ⟨4450729793839472059903961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967153195892981373269307 4450729793839472059903961)
          ·
            refine ⟨3338047345379604044927971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450729793839472059903961 3338047345379604044927971)
            ·
              refine ⟨5007071018069406067391957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338047345379604044927971 5007071018069406067391957)
              ·
                refine ⟨117353226986001704704499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5007071018069406067391957 117353226986001704704499)
                ·
                  rfl

theorem cell21_1542676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_1542676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542676 prefixEnd_1542676 := by exact prefixLift 1542676
  have htrace : WordTrace (prefixWord ++ tailWord_1542676) baseStart_1542676 baseEnd_1542676 := by
    simpa [prefixWord, tailWord_1542676, baseEnd_1542676] using wordTrace_append hprefix tailTrace_1542676
  have hstable : (prefixWord ++ tailWord_1542676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542676).length < 2 ^ (prefixWord ++ tailWord_1542676).sum := by decide
  have hdescent : baseEnd_1542676 < baseStart_1542676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542707 : List Nat := [1, 1, 1, 2, 4, 2, 5, 2, 3]
def baseStart_1542707 : Nat := 118140960795 + 1542707 * 2 ^ 59
def prefixEnd_1542707 : Nat := 4983230072969 + 3 ^ 40 * 1542707 * 2
def baseEnd_1542707 : Nat := 352066755580355949096767

theorem tailTrace_1542707 : CollatzResearch.WordTrace tailWord_1542707 prefixEnd_1542707 352066755580355949096767 := by
  unfold tailWord_1542707
  simp only [CollatzResearch.WordTrace]
  refine ⟨56267146822043487224522375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37511431214695658149681583 56267146822043487224522375)
  ·
    refine ⟨84400720233065230836783563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56267146822043487224522375 84400720233065230836783563)
    ·
      refine ⟨126601080349597846255175345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84400720233065230836783563 126601080349597846255175345)
      ·
        refine ⟨94950810262198384691381509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126601080349597846255175345 94950810262198384691381509)
        ·
          refine ⟨17803276924162197129634033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94950810262198384691381509 17803276924162197129634033)
          ·
            refine ⟨13352457693121647847225525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17803276924162197129634033 13352457693121647847225525)
            ·
              refine ⟨1251792908730154485677393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13352457693121647847225525 1251792908730154485677393)
              ·
                refine ⟨938844681547615864258045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251792908730154485677393 938844681547615864258045)
                ·
                  refine ⟨352066755580355949096767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938844681547615864258045 352066755580355949096767)
                  ·
                    rfl

theorem cell21_1542707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 3].length) (baseStart_1542707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542707 prefixEnd_1542707 := by exact prefixLift 1542707
  have htrace : WordTrace (prefixWord ++ tailWord_1542707) baseStart_1542707 baseEnd_1542707 := by
    simpa [prefixWord, tailWord_1542707, baseEnd_1542707] using wordTrace_append hprefix tailTrace_1542707
  have hstable : (prefixWord ++ tailWord_1542707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542707).length < 2 ^ (prefixWord ++ tailWord_1542707).sum := by decide
  have hdescent : baseEnd_1542707 < baseStart_1542707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542721 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 4]
def baseStart_1542721 : Nat := 118140960795 + 1542721 * 2 ^ 59
def prefixEnd_1542721 : Nat := 4983230072969 + 3 ^ 40 * 1542721 * 2
def baseEnd_1542721 : Nat := 352069950571095035863405

theorem tailTrace_1542721 : CollatzResearch.WordTrace tailWord_1542721 prefixEnd_1542721 352069950571095035863405 := by
  unfold tailWord_1542721
  simp only [CollatzResearch.WordTrace]
  refine ⟨56267657443992767615532017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37511771629328511743688011 56267657443992767615532017)
  ·
    refine ⟨42200743082994575711649013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56267657443992767615532017 42200743082994575711649013)
    ·
      refine ⟨3956319664030741472967095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42200743082994575711649013 3956319664030741472967095)
      ·
        refine ⟨5934479496046112209450643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956319664030741472967095 5934479496046112209450643)
        ·
          refine ⟨8901719244069168314175965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5934479496046112209450643 8901719244069168314175965)
          ·
            refine ⟨3338144716525938117815987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8901719244069168314175965 3338144716525938117815987)
            ·
              refine ⟨5007217074788907176723981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338144716525938117815987 5007217074788907176723981)
              ·
                refine ⟨1877706403045840191271493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5007217074788907176723981 1877706403045840191271493)
                ·
                  refine ⟨352069950571095035863405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877706403045840191271493 352069950571095035863405)
                  ·
                    rfl

theorem cell21_1542721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_1542721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542721 prefixEnd_1542721 := by exact prefixLift 1542721
  have htrace : WordTrace (prefixWord ++ tailWord_1542721) baseStart_1542721 baseEnd_1542721 := by
    simpa [prefixWord, tailWord_1542721, baseEnd_1542721] using wordTrace_append hprefix tailTrace_1542721
  have hstable : (prefixWord ++ tailWord_1542721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542721).length < 2 ^ (prefixWord ++ tailWord_1542721).sum := by decide
  have hdescent : baseEnd_1542721 < baseStart_1542721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542780 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_1542780 : Nat := 118140960795 + 1542780 * 2 ^ 59
def prefixEnd_1542780 : Nat := 4983230072969 + 3 ^ 40 * 1542780 * 2
def baseEnd_1542780 : Nat := 352083415174924044379951

theorem tailTrace_1542780 : CollatzResearch.WordTrace tailWord_1542780 prefixEnd_1542780 352083415174924044379951 := by
  unfold tailWord_1542780
  simp only [CollatzResearch.WordTrace]
  refine ⟨28134904675389510345964897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37513206233852680461286529 28134904675389510345964897)
  ·
    refine ⟨21101178506542132759473673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28134904675389510345964897 21101178506542132759473673)
    ·
      refine ⟨15825883879906599569605255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21101178506542132759473673 15825883879906599569605255)
      ·
        refine ⟨23738825819859899354407883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15825883879906599569605255 23738825819859899354407883)
        ·
          refine ⟨35608238729789849031611825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23738825819859899354407883 35608238729789849031611825)
          ·
            refine ⟨26706179047342386773708869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35608238729789849031611825 26706179047342386773708869)
            ·
              refine ⟨5007408571376697520070413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26706179047342386773708869 5007408571376697520070413)
              ·
                refine ⟨1877778214266261570026405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5007408571376697520070413 1877778214266261570026405)
                ·
                  refine ⟨352083415174924044379951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877778214266261570026405 352083415174924044379951)
                  ·
                    rfl

theorem cell21_1542780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_1542780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542780 prefixEnd_1542780 := by exact prefixLift 1542780
  have htrace : WordTrace (prefixWord ++ tailWord_1542780) baseStart_1542780 baseEnd_1542780 := by
    simpa [prefixWord, tailWord_1542780, baseEnd_1542780] using wordTrace_append hprefix tailTrace_1542780
  have hstable : (prefixWord ++ tailWord_1542780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542780).length < 2 ^ (prefixWord ++ tailWord_1542780).sum := by decide
  have hdescent : baseEnd_1542780 < baseStart_1542780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542935 : List Nat := [1, 1, 3, 4, 3, 1, 1, 4, 3]
def baseStart_1542935 : Nat := 118140960795 + 1542935 * 2 ^ 59
def prefixEnd_1542935 : Nat := 4983230072969 + 3 ^ 40 * 1542935 * 2
def baseEnd_1542935 : Nat := 352118788286678219296301

theorem tailTrace_1542935 : CollatzResearch.WordTrace tailWord_1542935 prefixEnd_1542935 352118788286678219296301 := by
  unfold tailWord_1542935
  simp only [CollatzResearch.WordTrace]
  refine ⟨56275462665217482163822259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37516975110144988109214839 56275462665217482163822259)
  ·
    refine ⟨84413193997826223245733389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56275462665217482163822259 84413193997826223245733389)
    ·
      refine ⟨31654947749184833717150021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84413193997826223245733389 31654947749184833717150021)
      ·
        refine ⟨5935302702972156321965629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31654947749184833717150021 5935302702972156321965629)
        ·
          refine ⟨2225738513614558620737111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5935302702972156321965629 2225738513614558620737111)
          ·
            refine ⟨3338607770421837931105667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225738513614558620737111 3338607770421837931105667)
            ·
              refine ⟨5007911655632756896658501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338607770421837931105667 5007911655632756896658501)
              ·
                refine ⟨938983435431141918123469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5007911655632756896658501 938983435431141918123469)
                ·
                  refine ⟨352118788286678219296301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938983435431141918123469 352118788286678219296301)
                  ·
                    rfl

theorem cell21_1542935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 3].length) (baseStart_1542935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542935 prefixEnd_1542935 := by exact prefixLift 1542935
  have htrace : WordTrace (prefixWord ++ tailWord_1542935) baseStart_1542935 baseEnd_1542935 := by
    simpa [prefixWord, tailWord_1542935, baseEnd_1542935] using wordTrace_append hprefix tailTrace_1542935
  have hstable : (prefixWord ++ tailWord_1542935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542935).length < 2 ^ (prefixWord ++ tailWord_1542935).sum := by decide
  have hdescent : baseEnd_1542935 < baseStart_1542935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542963 : List Nat := [1, 1, 1, 2, 6, 2, 3, 5]
def baseStart_1542963 : Nat := 118140960795 + 1542963 * 2 ^ 59
def prefixEnd_1542963 : Nat := 4983230072969 + 3 ^ 40 * 1542963 * 2
def baseEnd_1542963 : Nat := 117375059422718797609859

theorem tailTrace_1542963 : CollatzResearch.WordTrace tailWord_1542963 prefixEnd_1542963 117375059422718797609859 := by
  unfold tailWord_1542963
  simp only [CollatzResearch.WordTrace]
  refine ⟨56276483909116042945841543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37517655939410695297227695 56276483909116042945841543)
  ·
    refine ⟨84414725863674064418762315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56276483909116042945841543 84414725863674064418762315)
    ·
      refine ⟨126622088795511096628143473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84414725863674064418762315 126622088795511096628143473)
      ·
        refine ⟨94966566596633322471107605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126622088795511096628143473 94966566596633322471107605)
        ·
          refine ⟨4451557809217186990833169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94966566596633322471107605 4451557809217186990833169)
          ·
            refine ⟨3338668356912890243124877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4451557809217186990833169 3338668356912890243124877)
            ·
              refine ⟨1252000633842333841171829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3338668356912890243124877 1252000633842333841171829)
              ·
                refine ⟨117375059422718797609859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1252000633842333841171829 117375059422718797609859)
                ·
                  rfl

theorem cell21_1542963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 5].length) (baseStart_1542963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542963 prefixEnd_1542963 := by exact prefixLift 1542963
  have htrace : WordTrace (prefixWord ++ tailWord_1542963) baseStart_1542963 baseEnd_1542963 := by
    simpa [prefixWord, tailWord_1542963, baseEnd_1542963] using wordTrace_append hprefix tailTrace_1542963
  have hstable : (prefixWord ++ tailWord_1542963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542963).length < 2 ^ (prefixWord ++ tailWord_1542963).sum := by decide
  have hdescent : baseEnd_1542963 < baseStart_1542963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542980 : List Nat := [2, 3, 4, 2, 1, 1, 8]
def baseStart_1542980 : Nat := 118140960795 + 1542980 * 2 ^ 59
def prefixEnd_1542980 : Nat := 4983230072969 + 3 ^ 40 * 1542980 * 2
def baseEnd_1542980 : Nat := 39125450877752015671801

theorem tailTrace_1542980 : CollatzResearch.WordTrace tailWord_1542980 prefixEnd_1542980 39125450877752015671801 := by
  unfold tailWord_1542980
  simp only [CollatzResearch.WordTrace]
  refine ⟨28138551975027227424605197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37518069300036303232806929 28138551975027227424605197)
  ·
    refine ⟨10551956990635210284226949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28138551975027227424605197 10551956990635210284226949)
    ·
      refine ⟨1978491935744101928292553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10551956990635210284226949 1978491935744101928292553)
      ·
        refine ⟨1483868951808076446219415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1978491935744101928292553 1483868951808076446219415)
        ·
          refine ⟨2225803427712114669329123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483868951808076446219415 2225803427712114669329123)
          ·
            refine ⟨3338705141568172003993685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225803427712114669329123 3338705141568172003993685)
            ·
              refine ⟨39125450877752015671801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3338705141568172003993685 39125450877752015671801)
              ·
                rfl

theorem cell21_1542980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 8].length) (baseStart_1542980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542980 prefixEnd_1542980 := by exact prefixLift 1542980
  have htrace : WordTrace (prefixWord ++ tailWord_1542980) baseStart_1542980 baseEnd_1542980 := by
    simpa [prefixWord, tailWord_1542980, baseEnd_1542980] using wordTrace_append hprefix tailTrace_1542980
  have hstable : (prefixWord ++ tailWord_1542980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542980).length < 2 ^ (prefixWord ++ tailWord_1542980).sum := by decide
  have hdescent : baseEnd_1542980 < baseStart_1542980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542994 : List Nat := [3, 2, 2, 1, 1, 2, 1, 6, 3]
def baseStart_1542994 : Nat := 118140960795 + 1542994 * 2 ^ 59
def prefixEnd_1542994 : Nat := 4983230072969 + 3 ^ 40 * 1542994 * 2
def baseEnd_1542994 : Nat := 352132252890507227812847

theorem tailTrace_1542994 : CollatzResearch.WordTrace tailWord_1542994 prefixEnd_1542994 352132252890507227812847 := by
  unfold tailWord_1542994
  simp only [CollatzResearch.WordTrace]
  refine ⟨14069403643000933810055009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37518409714669156826813357 14069403643000933810055009)
  ·
    refine ⟨10552052732250700357541257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14069403643000933810055009 10552052732250700357541257)
    ·
      refine ⟨7914039549188025268155943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10552052732250700357541257 7914039549188025268155943)
      ·
        refine ⟨11871059323782037902233915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7914039549188025268155943 11871059323782037902233915)
        ·
          refine ⟨17806588985673056853350873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11871059323782037902233915 17806588985673056853350873)
          ·
            refine ⟨13354941739254792640013155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17806588985673056853350873 13354941739254792640013155)
            ·
              refine ⟨20032412608882188960019733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13354941739254792640013155 20032412608882188960019733)
              ·
                refine ⟨939019341041352607500925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20032412608882188960019733 939019341041352607500925)
                ·
                  refine ⟨352132252890507227812847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939019341041352607500925 352132252890507227812847)
                  ·
                    rfl

theorem cell21_1542994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_1542994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1542994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1542994 prefixEnd_1542994 := by exact prefixLift 1542994
  have htrace : WordTrace (prefixWord ++ tailWord_1542994) baseStart_1542994 baseEnd_1542994 := by
    simpa [prefixWord, tailWord_1542994, baseEnd_1542994] using wordTrace_append hprefix tailTrace_1542994
  have hstable : (prefixWord ++ tailWord_1542994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542994).length < 2 ^ (prefixWord ++ tailWord_1542994).sum := by decide
  have hdescent : baseEnd_1542994 < baseStart_1542994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543036 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_1543036 : Nat := 118140960795 + 1543036 * 2 ^ 59
def prefixEnd_1543036 : Nat := 4983230072969 + 3 ^ 40 * 1543036 * 2
def baseEnd_1543036 : Nat := 352141837862724488112761

theorem tailTrace_1543036 : CollatzResearch.WordTrace tailWord_1543036 prefixEnd_1543036 352141837862724488112761 := by
  unfold tailWord_1543036
  simp only [CollatzResearch.WordTrace]
  refine ⟨28139573218925788206624481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37519430958567717608832641 28139573218925788206624481)
  ·
    refine ⟨21104679914194341154968361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28139573218925788206624481 21104679914194341154968361)
    ·
      refine ⟨15828509935645755866226271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21104679914194341154968361 15828509935645755866226271)
      ·
        refine ⟨23742764903468633799339407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15828509935645755866226271 23742764903468633799339407)
        ·
          refine ⟨35614147355202950699009111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23742764903468633799339407 35614147355202950699009111)
          ·
            refine ⟨53421221032804426048513667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35614147355202950699009111 53421221032804426048513667)
            ·
              refine ⟨80131831549206639072770501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53421221032804426048513667 80131831549206639072770501)
              ·
                refine ⟨15024718415476244826144469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80131831549206639072770501 15024718415476244826144469)
                ·
                  refine ⟨352141837862724488112761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15024718415476244826144469 352141837862724488112761)
                  ·
                    rfl

theorem cell21_1543036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_1543036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543036 prefixEnd_1543036 := by exact prefixLift 1543036
  have htrace : WordTrace (prefixWord ++ tailWord_1543036) baseStart_1543036 baseEnd_1543036 := by
    simpa [prefixWord, tailWord_1543036, baseEnd_1543036] using wordTrace_append hprefix tailTrace_1543036
  have hstable : (prefixWord ++ tailWord_1543036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543036).length < 2 ^ (prefixWord ++ tailWord_1543036).sum := by decide
  have hdescent : baseEnd_1543036 < baseStart_1543036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543081 : List Nat := [1, 2, 1, 1, 1, 1, 5, 9]
def baseStart_1543081 : Nat := 118140960795 + 1543081 * 2 ^ 59
def prefixEnd_1543081 : Nat := 4983230072969 + 3 ^ 40 * 1543081 * 2
def baseEnd_1543081 : Nat := 117384035825271469954223

theorem tailTrace_1543081 : CollatzResearch.WordTrace tailWord_1543081 prefixEnd_1543081 117384035825271469954223 := by
  unfold tailWord_1543081
  simp only [CollatzResearch.WordTrace]
  refine ⟨56280787722688549098637097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37520525148459032732424731 56280787722688549098637097)
  ·
    refine ⟨42210590792016411823977823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56280787722688549098637097 42210590792016411823977823)
    ·
      refine ⟨63315886188024617735966735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42210590792016411823977823 63315886188024617735966735)
      ·
        refine ⟨94973829282036926603950103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63315886188024617735966735 94973829282036926603950103)
        ·
          refine ⟨142460743923055389905925155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94973829282036926603950103 142460743923055389905925155)
          ·
            refine ⟨213691115884583084858887733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142460743923055389905925155 213691115884583084858887733)
            ·
              refine ⟨20033542114179664205520725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213691115884583084858887733 20033542114179664205520725)
              ·
                refine ⟨117384035825271469954223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20033542114179664205520725 117384035825271469954223)
                ·
                  rfl

theorem cell21_1543081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 9].length) (baseStart_1543081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543081 prefixEnd_1543081 := by exact prefixLift 1543081
  have htrace : WordTrace (prefixWord ++ tailWord_1543081) baseStart_1543081 baseEnd_1543081 := by
    simpa [prefixWord, tailWord_1543081, baseEnd_1543081] using wordTrace_append hprefix tailTrace_1543081
  have hstable : (prefixWord ++ tailWord_1543081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543081).length < 2 ^ (prefixWord ++ tailWord_1543081).sum := by decide
  have hdescent : baseEnd_1543081 < baseStart_1543081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543101 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1543101 : Nat := 118140960795 + 1543101 * 2 ^ 59
def prefixEnd_1543101 : Nat := 4983230072969 + 3 ^ 40 * 1543101 * 2
def baseEnd_1543101 : Nat := 352156671748298819529295

theorem tailTrace_1543101 : CollatzResearch.WordTrace tailWord_1543101 prefixEnd_1543101 352156671748298819529295 := by
  unfold tailWord_1543101
  simp only [CollatzResearch.WordTrace]
  refine ⟨56281517182616092514365157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37521011455077395009576771 56281517182616092514365157)
  ·
    refine ⟨10552784471740517346443467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56281517182616092514365157 10552784471740517346443467)
    ·
      refine ⟨15829176707610776019665201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10552784471740517346443467 15829176707610776019665201)
      ·
        refine ⟨11871882530708082014748901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15829176707610776019665201 11871882530708082014748901)
        ·
          refine ⟨2225977974507765377765419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11871882530708082014748901 2225977974507765377765419)
          ·
            refine ⟨3338966961761648066648129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225977974507765377765419 3338966961761648066648129)
            ·
              refine ⟨2504225221321236049986097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3338966961761648066648129 2504225221321236049986097)
              ·
                refine ⟨1878168915990927037489573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2504225221321236049986097 1878168915990927037489573)
                ·
                  refine ⟨352156671748298819529295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1878168915990927037489573 352156671748298819529295)
                  ·
                    rfl

theorem cell21_1543101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1543101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543101 prefixEnd_1543101 := by exact prefixLift 1543101
  have htrace : WordTrace (prefixWord ++ tailWord_1543101) baseStart_1543101 baseEnd_1543101 := by
    simpa [prefixWord, tailWord_1543101, baseEnd_1543101] using wordTrace_append hprefix tailTrace_1543101
  have hstable : (prefixWord ++ tailWord_1543101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543101).length < 2 ^ (prefixWord ++ tailWord_1543101).sum := by decide
  have hdescent : baseEnd_1543101 < baseStart_1543101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543129 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 5]
def baseStart_1543129 : Nat := 118140960795 + 1543129 * 2 ^ 59
def prefixEnd_1543129 : Nat := 4983230072969 + 3 ^ 40 * 1543129 * 2
def baseEnd_1543129 : Nat := 352163061729776993062571

theorem tailTrace_1543129 : CollatzResearch.WordTrace tailWord_1543129 prefixEnd_1543129 352163061729776993062571 := by
  unfold tailWord_1543129
  simp only [CollatzResearch.WordTrace]
  refine ⟨56282538426514653296384441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37521692284343102197589627 56282538426514653296384441)
  ·
    refine ⟨42211903819885989972288331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56282538426514653296384441 42211903819885989972288331)
    ·
      refine ⟨63317855729828984958432497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42211903819885989972288331 63317855729828984958432497)
      ·
        refine ⟨47488391797371738718824373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63317855729828984958432497 47488391797371738718824373)
        ·
          refine ⟨4452036731003600504889785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47488391797371738718824373 4452036731003600504889785)
          ·
            refine ⟨3339027548252700378667339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4452036731003600504889785 3339027548252700378667339)
            ·
              refine ⟨5008541322379050568001009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339027548252700378667339 5008541322379050568001009)
              ·
                refine ⟨3756405991784287926000757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5008541322379050568001009 3756405991784287926000757)
                ·
                  refine ⟨352163061729776993062571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3756405991784287926000757 352163061729776993062571)
                  ·
                    rfl

theorem cell21_1543129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_1543129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543129 prefixEnd_1543129 := by exact prefixLift 1543129
  have htrace : WordTrace (prefixWord ++ tailWord_1543129) baseStart_1543129 baseEnd_1543129 := by
    simpa [prefixWord, tailWord_1543129, baseEnd_1543129] using wordTrace_append hprefix tailTrace_1543129
  have hstable : (prefixWord ++ tailWord_1543129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543129).length < 2 ^ (prefixWord ++ tailWord_1543129).sum := by decide
  have hdescent : baseEnd_1543129 < baseStart_1543129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543146 : List Nat := [3, 1, 3, 1, 2, 2, 1, 5, 3]
def baseStart_1543146 : Nat := 118140960795 + 1543146 * 2 ^ 59
def prefixEnd_1543146 : Nat := 4983230072969 + 3 ^ 40 * 1543146 * 2
def baseEnd_1543146 : Nat := 352166941361388741279203

theorem tailTrace_1543146 : CollatzResearch.WordTrace tailWord_1543146 prefixEnd_1543146 352166941361388741279203 := by
  unfold tailWord_1543146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14070789616863266299938323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37522105644968710133168861 14070789616863266299938323)
  ·
    refine ⟨21106184425294899449907485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14070789616863266299938323 21106184425294899449907485)
    ·
      refine ⟨7914819159485587293715307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21106184425294899449907485 7914819159485587293715307)
      ·
        refine ⟨11872228739228380940572961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7914819159485587293715307 11872228739228380940572961)
        ·
          refine ⟨8904171554421285705429721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11872228739228380940572961 8904171554421285705429721)
          ·
            refine ⟨6678128665815964279072291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8904171554421285705429721 6678128665815964279072291)
            ·
              refine ⟨10017192998723946418608437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678128665815964279072291 10017192998723946418608437)
              ·
                refine ⟨939111843630369976744541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10017192998723946418608437 939111843630369976744541)
                ·
                  refine ⟨352166941361388741279203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939111843630369976744541 352166941361388741279203)
                  ·
                    rfl

theorem cell21_1543146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_1543146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543146 prefixEnd_1543146 := by exact prefixLift 1543146
  have htrace : WordTrace (prefixWord ++ tailWord_1543146) baseStart_1543146 baseEnd_1543146 := by
    simpa [prefixWord, tailWord_1543146, baseEnd_1543146] using wordTrace_append hprefix tailTrace_1543146
  have hstable : (prefixWord ++ tailWord_1543146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543146).length < 2 ^ (prefixWord ++ tailWord_1543146).sum := by decide
  have hdescent : baseEnd_1543146 < baseStart_1543146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543191 : List Nat := [1, 1, 3, 5, 1, 1, 4, 5]
def baseStart_1543191 : Nat := 118140960795 + 1543191 * 2 ^ 59
def prefixEnd_1543191 : Nat := 4983230072969 + 3 ^ 40 * 1543191 * 2
def baseEnd_1543191 : Nat := 117392403658159554343037

theorem tailTrace_1543191 : CollatzResearch.WordTrace tailWord_1543191 prefixEnd_1543191 117392403658159554343037 := by
  unfold tailWord_1543191
  simp only [CollatzResearch.WordTrace]
  refine ⟨56284799752290037885141427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37523199834860025256760951 56284799752290037885141427)
  ·
    refine ⟨84427199628435056827712141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56284799752290037885141427 84427199628435056827712141)
    ·
      refine ⟨31660199860663146310392053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84427199628435056827712141 31660199860663146310392053)
      ·
        refine ⟨2968143736937169966599255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31660199860663146310392053 2968143736937169966599255)
        ·
          refine ⟨4452215605405754949898883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2968143736937169966599255 4452215605405754949898883)
          ·
            refine ⟨6678323408108632424848325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452215605405754949898883 6678323408108632424848325)
            ·
              refine ⟨1252185639020368579659061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6678323408108632424848325 1252185639020368579659061)
              ·
                refine ⟨117392403658159554343037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1252185639020368579659061 117392403658159554343037)
                ·
                  rfl

theorem cell21_1543191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 5].length) (baseStart_1543191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543191 prefixEnd_1543191 := by exact prefixLift 1543191
  have htrace : WordTrace (prefixWord ++ tailWord_1543191) baseStart_1543191 baseEnd_1543191 := by
    simpa [prefixWord, tailWord_1543191, baseEnd_1543191] using wordTrace_append hprefix tailTrace_1543191
  have hstable : (prefixWord ++ tailWord_1543191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543191).length < 2 ^ (prefixWord ++ tailWord_1543191).sum := by decide
  have hdescent : baseEnd_1543191 < baseStart_1543191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543219 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 4]
def baseStart_1543219 : Nat := 118140960795 + 1543219 * 2 ^ 59
def prefixEnd_1543219 : Nat := 4983230072969 + 3 ^ 40 * 1543219 * 2
def baseEnd_1543219 : Nat := 352183600955956836562387

theorem tailTrace_1543219 : CollatzResearch.WordTrace tailWord_1543219 prefixEnd_1543219 352183600955956836562387 := by
  unfold tailWord_1543219
  simp only [CollatzResearch.WordTrace]
  refine ⟨56285820996188598667160711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37523880664125732444773807 56285820996188598667160711)
  ·
    refine ⟨84428731494282898000741067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56285820996188598667160711 84428731494282898000741067)
    ·
      refine ⟨126643097241424347001111601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84428731494282898000741067 126643097241424347001111601)
      ·
        refine ⟨94982322931068260250833701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126643097241424347001111601 94982322931068260250833701)
        ·
          refine ⟨17809185549575298797031319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94982322931068260250833701 17809185549575298797031319)
          ·
            refine ⟨26713778324362948195546979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17809185549575298797031319 26713778324362948195546979)
            ·
              refine ⟨40070667486544422293320469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26713778324362948195546979 40070667486544422293320469)
              ·
                refine ⟨1878312538431769794999397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40070667486544422293320469 1878312538431769794999397)
                ·
                  refine ⟨352183600955956836562387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1878312538431769794999397 352183600955956836562387)
                  ·
                    rfl

theorem cell21_1543219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 4].length) (baseStart_1543219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543219 prefixEnd_1543219 := by exact prefixLift 1543219
  have htrace : WordTrace (prefixWord ++ tailWord_1543219) baseStart_1543219 baseEnd_1543219 := by
    simpa [prefixWord, tailWord_1543219, baseEnd_1543219] using wordTrace_append hprefix tailTrace_1543219
  have hstable : (prefixWord ++ tailWord_1543219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543219).length < 2 ^ (prefixWord ++ tailWord_1543219).sum := by decide
  have hdescent : baseEnd_1543219 < baseStart_1543219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543222 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1543222 : Nat := 118140960795 + 1543222 * 2 ^ 59
def prefixEnd_1543222 : Nat := 4983230072969 + 3 ^ 40 * 1543222 * 2
def baseEnd_1543222 : Nat := 352184285596829498012381

theorem tailTrace_1543222 : CollatzResearch.WordTrace tailWord_1543222 prefixEnd_1543222 352184285596829498012381 := by
  unfold tailWord_1543222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517870650948608136219995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37523953610118486786346613 3517870650948608136219995)
  ·
    refine ⟨5276805976422912204329993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3517870650948608136219995 5276805976422912204329993)
    ·
      refine ⟨3957604482317184153247495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5276805976422912204329993 3957604482317184153247495)
      ·
        refine ⟨5936406723475776229871243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957604482317184153247495 5936406723475776229871243)
        ·
          refine ⟨8904610085213664344806865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5936406723475776229871243 8904610085213664344806865)
          ·
            refine ⟨6678457563910248258605149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8904610085213664344806865 6678457563910248258605149)
            ·
              refine ⟨2504421586466343096976931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6678457563910248258605149 2504421586466343096976931)
              ·
                refine ⟨3756632379699514645465397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504421586466343096976931 3756632379699514645465397)
                ·
                  refine ⟨352184285596829498012381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3756632379699514645465397 352184285596829498012381)
                  ·
                    rfl

theorem cell21_1543222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1543222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543222 prefixEnd_1543222 := by exact prefixLift 1543222
  have htrace : WordTrace (prefixWord ++ tailWord_1543222) baseStart_1543222 baseEnd_1543222 := by
    simpa [prefixWord, tailWord_1543222, baseEnd_1543222] using wordTrace_append hprefix tailTrace_1543222
  have hstable : (prefixWord ++ tailWord_1543222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543222).length < 2 ^ (prefixWord ++ tailWord_1543222).sum := by decide
  have hdescent : baseEnd_1543222 < baseStart_1543222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543250 : List Nat := [3, 2, 2, 1, 3, 1, 2, 7]
def baseStart_1543250 : Nat := 118140960795 + 1543250 * 2 ^ 59
def prefixEnd_1543250 : Nat := 4983230072969 + 3 ^ 40 * 1543250 * 2
def baseEnd_1543250 : Nat := 117396891859435890515219

theorem tailTrace_1543250 : CollatzResearch.WordTrace tailWord_1543250 prefixEnd_1543250 117396891859435890515219 := by
  unfold tailWord_1543250
  simp only [CollatzResearch.WordTrace]
  refine ⟨14071737914769072740384801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37524634439384193974359469 14071737914769072740384801)
  ·
    refine ⟨10553803436076804555288601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14071737914769072740384801 10553803436076804555288601)
    ·
      refine ⟨7915352577057603416466451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10553803436076804555288601 7915352577057603416466451)
      ·
        refine ⟨11873028865586405124699677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915352577057603416466451 11873028865586405124699677)
        ·
          refine ⟨4452385824594901921762379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11873028865586405124699677 4452385824594901921762379)
          ·
            refine ⟨6678578736892352882643569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452385824594901921762379 6678578736892352882643569)
            ·
              refine ⟨5008934052669264661982677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6678578736892352882643569 5008934052669264661982677)
              ·
                refine ⟨117396891859435890515219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5008934052669264661982677 117396891859435890515219)
                ·
                  rfl

theorem cell21_1543250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_1543250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543250 prefixEnd_1543250 := by exact prefixLift 1543250
  have htrace : WordTrace (prefixWord ++ tailWord_1543250) baseStart_1543250 baseEnd_1543250 := by
    simpa [prefixWord, tailWord_1543250, baseEnd_1543250] using wordTrace_append hprefix tailTrace_1543250
  have hstable : (prefixWord ++ tailWord_1543250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543250).length < 2 ^ (prefixWord ++ tailWord_1543250).sum := by decide
  have hdescent : baseEnd_1543250 < baseStart_1543250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543360 : List Nat := [2, 1, 1, 2, 7, 1, 2, 5]
def baseStart_1543360 : Nat := 118140960795 + 1543360 * 2 ^ 59
def prefixEnd_1543360 : Nat := 4983230072969 + 3 ^ 40 * 1543360 * 2
def baseEnd_1543360 : Nat := 117405259692323974904033

theorem tailTrace_1543360 : CollatzResearch.WordTrace tailWord_1543360 prefixEnd_1543360 117405259692323974904033 := by
  unfold tailWord_1543360
  simp only [CollatzResearch.WordTrace]
  refine ⟨28145481844338889874021767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37527309125785186498695689 28145481844338889874021767)
  ·
    refine ⟨42218222766508334811032651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28145481844338889874021767 42218222766508334811032651)
    ·
      refine ⟨63327334149762502216548977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42218222766508334811032651 63327334149762502216548977)
      ·
        refine ⟨47495500612321876662411733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63327334149762502216548977 47495500612321876662411733)
        ·
          refine ⟨1113175795601293984275275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47495500612321876662411733 1113175795601293984275275)
          ·
            refine ⟨1669763693401940976412913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113175795601293984275275 1669763693401940976412913)
            ·
              refine ⟨1252322770051455732309685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669763693401940976412913 1252322770051455732309685)
              ·
                refine ⟨117405259692323974904033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1252322770051455732309685 117405259692323974904033)
                ·
                  rfl

theorem cell21_1543360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 5].length) (baseStart_1543360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543360 prefixEnd_1543360 := by exact prefixLift 1543360
  have htrace : WordTrace (prefixWord ++ tailWord_1543360) baseStart_1543360 baseEnd_1543360 := by
    simpa [prefixWord, tailWord_1543360, baseEnd_1543360] using wordTrace_append hprefix tailTrace_1543360
  have hstable : (prefixWord ++ tailWord_1543360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543360).length < 2 ^ (prefixWord ++ tailWord_1543360).sum := by decide
  have hdescent : baseEnd_1543360 < baseStart_1543360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543366 : List Nat := [6, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1543366 : Nat := 118140960795 + 1543366 * 2 ^ 59
def prefixEnd_1543366 : Nat := 4983230072969 + 3 ^ 40 * 1543366 * 2
def baseEnd_1543366 : Nat := 352217148358717247612087

theorem tailTrace_1543366 : CollatzResearch.WordTrace tailWord_1543366 prefixEnd_1543366 352217148358717247612087 := by
  unfold tailWord_1543366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759099453958001336648811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37527455017770695181841301 1759099453958001336648811)
  ·
    refine ⟨2638649180937002004973217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1759099453958001336648811 2638649180937002004973217)
    ·
      refine ⟨1978986885702751503729913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2638649180937002004973217 1978986885702751503729913)
      ·
        refine ⟨1484240164277063627797435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1978986885702751503729913 1484240164277063627797435)
        ·
          refine ⟨2226360246415595441696153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1484240164277063627797435 2226360246415595441696153)
          ·
            refine ⟨1669770184811696581272115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2226360246415595441696153 1669770184811696581272115)
            ·
              refine ⟨2504655277217544871908173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669770184811696581272115 2504655277217544871908173)
              ·
                refine ⟨939245728956579326965565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2504655277217544871908173 939245728956579326965565)
                ·
                  refine ⟨352217148358717247612087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939245728956579326965565 352217148358717247612087)
                  ·
                    rfl

theorem cell21_1543366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1543366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543366 prefixEnd_1543366 := by exact prefixLift 1543366
  have htrace : WordTrace (prefixWord ++ tailWord_1543366) baseStart_1543366 baseEnd_1543366 := by
    simpa [prefixWord, tailWord_1543366, baseEnd_1543366] using wordTrace_append hprefix tailTrace_1543366
  have hstable : (prefixWord ++ tailWord_1543366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543366).length < 2 ^ (prefixWord ++ tailWord_1543366).sum := by decide
  have hdescent : baseEnd_1543366 < baseStart_1543366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543402 : List Nat := [3, 1, 3, 1, 1, 4, 2, 6]
def baseStart_1543402 : Nat := 118140960795 + 1543402 * 2 ^ 59
def prefixEnd_1543402 : Nat := 4983230072969 + 3 ^ 40 * 1543402 * 2
def baseEnd_1543402 : Nat := 117408454683063061670671

theorem tailTrace_1543402 : CollatzResearch.WordTrace tailWord_1543402 prefixEnd_1543402 117408454683063061670671 := by
  unfold tailWord_1543402
  simp only [CollatzResearch.WordTrace]
  refine ⟨14073123888631405230268115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37528330369683747280714973 14073123888631405230268115)
  ·
    refine ⟨21109685832947107845402173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14073123888631405230268115 21109685832947107845402173)
    ·
      refine ⟨7916132187355165442025815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21109685832947107845402173 7916132187355165442025815)
      ·
        refine ⟨11874198281032748163038723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7916132187355165442025815 11874198281032748163038723)
        ·
          refine ⟨17811297421549122244558085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11874198281032748163038723 17811297421549122244558085)
          ·
            refine ⟨3339618266540460420854641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17811297421549122244558085 3339618266540460420854641)
            ·
              refine ⟨2504713699905345315640981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3339618266540460420854641 2504713699905345315640981)
              ·
                refine ⟨117408454683063061670671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2504713699905345315640981 117408454683063061670671)
                ·
                  rfl

theorem cell21_1543402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_1543402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543402 prefixEnd_1543402 := by exact prefixLift 1543402
  have htrace : WordTrace (prefixWord ++ tailWord_1543402) baseStart_1543402 baseEnd_1543402 := by
    simpa [prefixWord, tailWord_1543402, baseEnd_1543402] using wordTrace_append hprefix tailTrace_1543402
  have hstable : (prefixWord ++ tailWord_1543402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543402).length < 2 ^ (prefixWord ++ tailWord_1543402).sum := by decide
  have hdescent : baseEnd_1543402 < baseStart_1543402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543405 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1543405 : Nat := 118140960795 + 1543405 * 2 ^ 59
def prefixEnd_1543405 : Nat := 4983230072969 + 3 ^ 40 * 1543405 * 2
def baseEnd_1543405 : Nat := 352226048690061846462007

theorem tailTrace_1543405 : CollatzResearch.WordTrace tailWord_1543405 prefixEnd_1543405 352226048690061846462007 := by
  unfold tailWord_1543405
  simp only [CollatzResearch.WordTrace]
  refine ⟨56292604973514752433431669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37528403315676501622287779 56292604973514752433431669)
  ·
    refine ⟨5277431716267008040634219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56292604973514752433431669 5277431716267008040634219)
    ·
      refine ⟨7916147574400512060951329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5277431716267008040634219 7916147574400512060951329)
      ·
        refine ⟨5937110680800384045713497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7916147574400512060951329 5937110680800384045713497)
        ·
          refine ⟨4452833010600288034285123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5937110680800384045713497 4452833010600288034285123)
          ·
            refine ⟨6679249515900432051427685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452833010600288034285123 6679249515900432051427685)
            ·
              refine ⟨1252359284231331009642691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6679249515900432051427685 1252359284231331009642691)
              ·
                refine ⟨1878538926346996514464037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252359284231331009642691 1878538926346996514464037)
                ·
                  refine ⟨352226048690061846462007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1878538926346996514464037 352226048690061846462007)
                  ·
                    rfl

theorem cell21_1543405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1543405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543405 prefixEnd_1543405 := by exact prefixLift 1543405
  have htrace : WordTrace (prefixWord ++ tailWord_1543405) baseStart_1543405 baseEnd_1543405 := by
    simpa [prefixWord, tailWord_1543405, baseEnd_1543405] using wordTrace_append hprefix tailTrace_1543405
  have hstable : (prefixWord ++ tailWord_1543405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543405).length < 2 ^ (prefixWord ++ tailWord_1543405).sum := by decide
  have hdescent : baseEnd_1543405 < baseStart_1543405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543433 : List Nat := [1, 2, 1, 1, 3, 3, 2, 5, 3]
def baseStart_1543433 : Nat := 118140960795 + 1543433 * 2 ^ 59
def prefixEnd_1543433 : Nat := 4983230072969 + 3 ^ 40 * 1543433 * 2
def baseEnd_1543433 : Nat := 352232438671540019995283

theorem tailTrace_1543433 : CollatzResearch.WordTrace tailWord_1543433 prefixEnd_1543433 352232438671540019995283 := by
  unfold tailWord_1543433
  simp only [CollatzResearch.WordTrace]
  refine ⟨56293626217413313215450953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37529084144942208810300635 56293626217413313215450953)
  ·
    refine ⟨42220219663059984911588215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56293626217413313215450953 42220219663059984911588215)
    ·
      refine ⟨63330329494589977367382323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42220219663059984911588215 63330329494589977367382323)
      ·
        refine ⟨94995494241884966051073485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63330329494589977367382323 94995494241884966051073485)
        ·
          refine ⟨35623310340706862269152557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94995494241884966051073485 35623310340706862269152557)
          ·
            refine ⟨13358741377765073350932209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35623310340706862269152557 13358741377765073350932209)
            ·
              refine ⟨10019056033323805013199157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13358741377765073350932209 10019056033323805013199157)
              ·
                refine ⟨939286503124106719987421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10019056033323805013199157 939286503124106719987421)
                ·
                  refine ⟨352232438671540019995283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939286503124106719987421 352232438671540019995283)
                  ·
                    rfl

theorem cell21_1543433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 3].length) (baseStart_1543433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543433 prefixEnd_1543433 := by exact prefixLift 1543433
  have htrace : WordTrace (prefixWord ++ tailWord_1543433) baseStart_1543433 baseEnd_1543433 := by
    simpa [prefixWord, tailWord_1543433, baseEnd_1543433] using wordTrace_append hprefix tailTrace_1543433
  have hstable : (prefixWord ++ tailWord_1543433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543433).length < 2 ^ (prefixWord ++ tailWord_1543433).sum := by decide
  have hdescent : baseEnd_1543433 < baseStart_1543433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543442 : List Nat := [3, 2, 4, 2, 2, 1, 2, 2, 3]
def baseStart_1543442 : Nat := 118140960795 + 1543442 * 2 ^ 59
def prefixEnd_1543442 : Nat := 4983230072969 + 3 ^ 40 * 1543442 * 2
def baseEnd_1543442 : Nat := 352234492594158004345265

theorem tailTrace_1543442 : CollatzResearch.WordTrace tailWord_1543442 prefixEnd_1543442 352234492594158004345265 := by
  unfold tailWord_1543442
  simp only [CollatzResearch.WordTrace]
  refine ⟨14073488618595176938132145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37529302982920471835019053 14073488618595176938132145)
  ·
    refine ⟨10555116463946382703599109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14073488618595176938132145 10555116463946382703599109)
    ·
      refine ⟨1979084336989946756924833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10555116463946382703599109 1979084336989946756924833)
      ·
        refine ⟨1484313252742460067693625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1979084336989946756924833 1484313252742460067693625)
        ·
          refine ⟨1113234939556845050770219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1484313252742460067693625 1113234939556845050770219)
          ·
            refine ⟨1669852409335267576155329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113234939556845050770219 1669852409335267576155329)
            ·
              refine ⟨1252389307001450682116497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669852409335267576155329 1252389307001450682116497)
              ·
                refine ⟨939291980251088011587373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252389307001450682116497 939291980251088011587373)
                ·
                  refine ⟨352234492594158004345265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939291980251088011587373 352234492594158004345265)
                  ·
                    rfl

theorem cell21_1543442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_1543442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543442 prefixEnd_1543442 := by exact prefixLift 1543442
  have htrace : WordTrace (prefixWord ++ tailWord_1543442) baseStart_1543442 baseEnd_1543442 := by
    simpa [prefixWord, tailWord_1543442, baseEnd_1543442] using wordTrace_append hprefix tailTrace_1543442
  have hstable : (prefixWord ++ tailWord_1543442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543442).length < 2 ^ (prefixWord ++ tailWord_1543442).sum := by decide
  have hdescent : baseEnd_1543442 < baseStart_1543442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543450 : List Nat := [3, 1, 1, 3, 3, 2, 1, 4, 3]
def baseStart_1543450 : Nat := 118140960795 + 1543450 * 2 ^ 59
def prefixEnd_1543450 : Nat := 4983230072969 + 3 ^ 40 * 1543450 * 2
def baseEnd_1543450 : Nat := 352236318303151768211915

theorem tailTrace_1543450 : CollatzResearch.WordTrace tailWord_1543450 prefixEnd_1543450 352236318303151768211915 := by
  unfold tailWord_1543450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14073561564587931279704951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37529497505567816745879869 14073561564587931279704951)
  ·
    refine ⟨21110342346881896919557427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14073561564587931279704951 21110342346881896919557427)
    ·
      refine ⟨31665513520322845379336141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21110342346881896919557427 31665513520322845379336141)
      ·
        refine ⟨11874567570121067017251053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31665513520322845379336141 11874567570121067017251053)
        ·
          refine ⟨4452962838795400131469145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11874567570121067017251053 4452962838795400131469145)
          ·
            refine ⟨3339722129096550098601859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4452962838795400131469145 3339722129096550098601859)
            ·
              refine ⟨5009583193644825147902789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339722129096550098601859 5009583193644825147902789)
              ·
                refine ⟨939296848808404715231773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5009583193644825147902789 939296848808404715231773)
                ·
                  refine ⟨352236318303151768211915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939296848808404715231773 352236318303151768211915)
                  ·
                    rfl

theorem cell21_1543450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_1543450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543450 prefixEnd_1543450 := by exact prefixLift 1543450
  have htrace : WordTrace (prefixWord ++ tailWord_1543450) baseStart_1543450 baseEnd_1543450 := by
    simpa [prefixWord, tailWord_1543450, baseEnd_1543450] using wordTrace_append hprefix tailTrace_1543450
  have hstable : (prefixWord ++ tailWord_1543450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543450).length < 2 ^ (prefixWord ++ tailWord_1543450).sum := by decide
  have hdescent : baseEnd_1543450 < baseStart_1543450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543464 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_1543464 : Nat := 118140960795 + 1543464 * 2 ^ 59
def prefixEnd_1543464 : Nat := 4983230072969 + 3 ^ 40 * 1543464 * 2
def baseEnd_1543464 : Nat := 352239513293890854978553

theorem tailTrace_1543464 : CollatzResearch.WordTrace tailWord_1543464 prefixEnd_1543464 352239513293890854978553 := by
  unfold tailWord_1543464
  simp only [CollatzResearch.WordTrace]
  refine ⟨28147378440150502754914723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37529837920200670339886297 28147378440150502754914723)
  ·
    refine ⟨42221067660225754132372085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28147378440150502754914723 42221067660225754132372085)
    ·
      refine ⟨3958225093146164449909883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42221067660225754132372085 3958225093146164449909883)
      ·
        refine ⟨5937337639719246674864825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3958225093146164449909883 5937337639719246674864825)
        ·
          refine ⟨4453003229789435006148619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5937337639719246674864825 4453003229789435006148619)
          ·
            refine ⟨6679504844684152509222929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453003229789435006148619 6679504844684152509222929)
            ·
              refine ⟨5009628633513114381917197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6679504844684152509222929 5009628633513114381917197)
              ·
                refine ⟨1878610737567417893218949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5009628633513114381917197 1878610737567417893218949)
                ·
                  refine ⟨352239513293890854978553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1878610737567417893218949 352239513293890854978553)
                  ·
                    rfl

theorem cell21_1543464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_1543464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543464 prefixEnd_1543464 := by exact prefixLift 1543464
  have htrace : WordTrace (prefixWord ++ tailWord_1543464) baseStart_1543464 baseEnd_1543464 := by
    simpa [prefixWord, tailWord_1543464, baseEnd_1543464] using wordTrace_append hprefix tailTrace_1543464
  have hstable : (prefixWord ++ tailWord_1543464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543464).length < 2 ^ (prefixWord ++ tailWord_1543464).sum := by decide
  have hdescent : baseEnd_1543464 < baseStart_1543464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543509 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 5]
def baseStart_1543509 : Nat := 118140960795 + 1543509 * 2 ^ 59
def prefixEnd_1543509 : Nat := 4983230072969 + 3 ^ 40 * 1543509 * 2
def baseEnd_1543509 : Nat := 352249782906980776728461

theorem tailTrace_1543509 : CollatzResearch.WordTrace tailWord_1543509 prefixEnd_1543509 352249782906980776728461 := by
  unfold tailWord_1543509
  simp only [CollatzResearch.WordTrace]
  refine ⟨56296398165137978195217581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37530932110091985463478387 56296398165137978195217581)
  ·
    refine ⟨21111149311926741823206593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56296398165137978195217581 21111149311926741823206593)
    ·
      refine ⟨15833361983945056367404945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21111149311926741823206593 15833361983945056367404945)
      ·
        refine ⟨11875021487958792275553709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15833361983945056367404945 11875021487958792275553709)
        ·
          refine ⟨4453133057984547103332641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11875021487958792275553709 4453133057984547103332641)
          ·
            refine ⟨3339849793488410327499481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4453133057984547103332641 3339849793488410327499481)
            ·
              refine ⟨2504887345116307745624611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3339849793488410327499481 2504887345116307745624611)
              ·
                refine ⟨3757331017674461618436917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504887345116307745624611 3757331017674461618436917)
                ·
                  refine ⟨352249782906980776728461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3757331017674461618436917 352249782906980776728461)
                  ·
                    rfl

theorem cell21_1543509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_1543509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543509 prefixEnd_1543509 := by exact prefixLift 1543509
  have htrace : WordTrace (prefixWord ++ tailWord_1543509) baseStart_1543509 baseEnd_1543509 := by
    simpa [prefixWord, tailWord_1543509, baseEnd_1543509] using wordTrace_append hprefix tailTrace_1543509
  have hstable : (prefixWord ++ tailWord_1543509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543509).length < 2 ^ (prefixWord ++ tailWord_1543509).sum := by decide
  have hdescent : baseEnd_1543509 < baseStart_1543509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543737 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 5]
def baseStart_1543737 : Nat := 118140960795 + 1543737 * 2 ^ 59
def prefixEnd_1543737 : Nat := 4983230072969 + 3 ^ 40 * 1543737 * 2
def baseEnd_1543737 : Nat := 352301815613303046927995

theorem tailTrace_1543737 : CollatzResearch.WordTrace tailWord_1543737 prefixEnd_1543737 352301815613303046927995 := by
  unfold tailWord_1543737
  simp only [CollatzResearch.WordTrace]
  refine ⟨56304714008311973134517465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37536476005541315423011643 56304714008311973134517465)
  ·
    refine ⟨42228535506233979850888099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56304714008311973134517465 42228535506233979850888099)
    ·
      refine ⟨63342803259350969776332149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42228535506233979850888099 63342803259350969776332149)
      ·
        refine ⟨5938387805564153416531139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63342803259350969776332149 5938387805564153416531139)
        ·
          refine ⟨8907581708346230124796709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5938387805564153416531139 8907581708346230124796709)
          ·
            refine ⟨1670171570314918148399383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8907581708346230124796709 1670171570314918148399383)
            ·
              refine ⟨2505257355472377222599075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670171570314918148399383 2505257355472377222599075)
              ·
                refine ⟨3757886033208565833898613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505257355472377222599075 3757886033208565833898613)
                ·
                  refine ⟨352301815613303046927995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3757886033208565833898613 352301815613303046927995)
                  ·
                    rfl

theorem cell21_1543737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_1543737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543737 prefixEnd_1543737 := by exact prefixLift 1543737
  have htrace : WordTrace (prefixWord ++ tailWord_1543737) baseStart_1543737 baseEnd_1543737 := by
    simpa [prefixWord, tailWord_1543737, baseEnd_1543737] using wordTrace_append hprefix tailTrace_1543737
  have hstable : (prefixWord ++ tailWord_1543737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543737).length < 2 ^ (prefixWord ++ tailWord_1543737).sum := by decide
  have hdescent : baseEnd_1543737 < baseStart_1543737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543824 : List Nat := [2, 1, 1, 1, 1, 1, 3, 11]
def baseStart_1543824 : Nat := 118140960795 + 1543824 * 2 ^ 59
def prefixEnd_1543824 : Nat := 4983230072969 + 3 ^ 40 * 1543824 * 2
def baseEnd_1543824 : Nat := 117440556732870076325939

theorem tailTrace_1543824 : CollatzResearch.WordTrace tailWord_1543824 prefixEnd_1543824 117440556732870076325939 := by
  unfold tailWord_1543824
  simp only [CollatzResearch.WordTrace]
  refine ⟨28153943579498393496467263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37538591439331191328623017 28153943579498393496467263)
  ·
    refine ⟨42230915369247590244700895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28153943579498393496467263 42230915369247590244700895)
    ·
      refine ⟨63346373053871385367051343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42230915369247590244700895 63346373053871385367051343)
      ·
        refine ⟨95019559580807078050577015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63346373053871385367051343 95019559580807078050577015)
        ·
          refine ⟨142529339371210617075865523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95019559580807078050577015 142529339371210617075865523)
          ·
            refine ⟨213794009056815925613798285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142529339371210617075865523 213794009056815925613798285)
            ·
              refine ⟨80172753396305972105174357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213794009056815925613798285 80172753396305972105174357)
              ·
                refine ⟨117440556732870076325939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 80172753396305972105174357 117440556732870076325939)
                ·
                  rfl

theorem cell21_1543824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_1543824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543824 prefixEnd_1543824 := by exact prefixLift 1543824
  have htrace : WordTrace (prefixWord ++ tailWord_1543824) baseStart_1543824 baseEnd_1543824 := by
    simpa [prefixWord, tailWord_1543824, baseEnd_1543824] using wordTrace_append hprefix tailTrace_1543824
  have hstable : (prefixWord ++ tailWord_1543824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543824).length < 2 ^ (prefixWord ++ tailWord_1543824).sum := by decide
  have hdescent : baseEnd_1543824 < baseStart_1543824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543841 : List Nat := [1, 2, 3, 3, 2, 2, 8]
def baseStart_1543841 : Nat := 118140960795 + 1543841 * 2 ^ 59
def prefixEnd_1543841 : Nat := 4983230072969 + 3 ^ 40 * 1543841 * 2
def baseEnd_1543841 : Nat := 39147283314469108577161

theorem tailTrace_1543841 : CollatzResearch.WordTrace tailWord_1543841 prefixEnd_1543841 39147283314469108577161 := by
  unfold tailWord_1543841
  simp only [CollatzResearch.WordTrace]
  refine ⟨56308507199935198896303377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37539004799956799264202251 56308507199935198896303377)
  ·
    refine ⟨42231380399951399172227533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56308507199935198896303377 42231380399951399172227533)
    ·
      refine ⟨15836767649981774689585325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42231380399951399172227533 15836767649981774689585325)
      ·
        refine ⟨5938787868743165508594497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15836767649981774689585325 5938787868743165508594497)
        ·
          refine ⟨4454090901557374131445873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5938787868743165508594497 4454090901557374131445873)
          ·
            refine ⟨3340568176168030598584405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4454090901557374131445873 3340568176168030598584405)
            ·
              refine ⟨39147283314469108577161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3340568176168030598584405 39147283314469108577161)
              ·
                rfl

theorem cell21_1543841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 8].length) (baseStart_1543841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543841 prefixEnd_1543841 := by exact prefixLift 1543841
  have htrace : WordTrace (prefixWord ++ tailWord_1543841) baseStart_1543841 baseEnd_1543841 := by
    simpa [prefixWord, tailWord_1543841, baseEnd_1543841] using wordTrace_append hprefix tailTrace_1543841
  have hstable : (prefixWord ++ tailWord_1543841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543841).length < 2 ^ (prefixWord ++ tailWord_1543841).sum := by decide
  have hdescent : baseEnd_1543841 < baseStart_1543841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543844 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 4]
def baseStart_1543844 : Nat := 118140960795 + 1543844 * 2 ^ 59
def prefixEnd_1543844 : Nat := 4983230072969 + 3 ^ 40 * 1543844 * 2
def baseEnd_1543844 : Nat := 352326234471094638644443

theorem tailTrace_1543844 : CollatzResearch.WordTrace tailWord_1543844 prefixEnd_1543844 352326234471094638644443 := by
  unfold tailWord_1543844
  simp only [CollatzResearch.WordTrace]
  refine ⟨28154308309462165204331293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37539077745949553605775057 28154308309462165204331293)
  ·
    refine ⟨10557865616048311951624235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28154308309462165204331293 10557865616048311951624235)
    ·
      refine ⟨15836798424072467927436353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10557865616048311951624235 15836798424072467927436353)
      ·
        refine ⟨11877598818054350945577265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15836798424072467927436353 11877598818054350945577265)
        ·
          refine ⟨8908199113540763209182949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11877598818054350945577265 8908199113540763209182949)
          ·
            refine ⟨1670287333788893101721803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8908199113540763209182949 1670287333788893101721803)
            ·
              refine ⟨2505431000683339652582705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670287333788893101721803 2505431000683339652582705)
              ·
                refine ⟨1879073250512504739437029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2505431000683339652582705 1879073250512504739437029)
                ·
                  refine ⟨352326234471094638644443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1879073250512504739437029 352326234471094638644443)
                  ·
                    rfl

theorem cell21_1543844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_1543844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543844 prefixEnd_1543844 := by exact prefixLift 1543844
  have htrace : WordTrace (prefixWord ++ tailWord_1543844) baseStart_1543844 baseEnd_1543844 := by
    simpa [prefixWord, tailWord_1543844, baseEnd_1543844] using wordTrace_append hprefix tailTrace_1543844
  have hstable : (prefixWord ++ tailWord_1543844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543844).length < 2 ^ (prefixWord ++ tailWord_1543844).sum := by decide
  have hdescent : baseEnd_1543844 < baseStart_1543844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543861 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 4]
def baseStart_1543861 : Nat := 118140960795 + 1543861 * 2 ^ 59
def prefixEnd_1543861 : Nat := 4983230072969 + 3 ^ 40 * 1543861 * 2
def baseEnd_1543861 : Nat := 352330114102706386861075

theorem tailTrace_1543861 : CollatzResearch.WordTrace tailWord_1543861 prefixEnd_1543861 352330114102706386861075 := by
  unfold tailWord_1543861
  simp only [CollatzResearch.WordTrace]
  refine ⟨56309236659862742312031437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37539491106575161541354291 56309236659862742312031437)
  ·
    refine ⟨21115963747448528367011789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56309236659862742312031437 21115963747448528367011789)
    ·
      refine ⟨7918486405293198137629421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21115963747448528367011789 7918486405293198137629421)
      ·
        refine ⟨2969432401984949301611033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7918486405293198137629421 2969432401984949301611033)
        ·
          refine ⟨2227074301488711976208275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2969432401984949301611033 2227074301488711976208275)
          ·
            refine ⟨3340611452233067964312413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227074301488711976208275 3340611452233067964312413)
            ·
              refine ⟨1252729294587400486617155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3340611452233067964312413 1252729294587400486617155)
              ·
                refine ⟨1879093941881100729925733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252729294587400486617155 1879093941881100729925733)
                ·
                  refine ⟨352330114102706386861075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1879093941881100729925733 352330114102706386861075)
                  ·
                    rfl

theorem cell21_1543861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_1543861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543861 prefixEnd_1543861 := by exact prefixLift 1543861
  have htrace : WordTrace (prefixWord ++ tailWord_1543861) baseStart_1543861 baseEnd_1543861 := by
    simpa [prefixWord, tailWord_1543861, baseEnd_1543861] using wordTrace_append hprefix tailTrace_1543861
  have hstable : (prefixWord ++ tailWord_1543861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543861).length < 2 ^ (prefixWord ++ tailWord_1543861).sum := by decide
  have hdescent : baseEnd_1543861 < baseStart_1543861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543886 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_1543886 : Nat := 118140960795 + 1543886 * 2 ^ 59
def prefixEnd_1543886 : Nat := 4983230072969 + 3 ^ 40 * 1543886 * 2
def baseEnd_1543886 : Nat := 352335819443311898944357

theorem tailTrace_1543886 : CollatzResearch.WordTrace tailWord_1543886 prefixEnd_1543886 352335819443311898944357 := by
  unfold tailWord_1543886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7038768560596521447711439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37540098989848114387794341 7038768560596521447711439)
  ·
    refine ⟨10558152840894782171567159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7038768560596521447711439 10558152840894782171567159)
    ·
      refine ⟨15837229261342173257350739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10558152840894782171567159 15837229261342173257350739)
      ·
        refine ⟨23755843892013259886026109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15837229261342173257350739 23755843892013259886026109)
        ·
          refine ⟨8908441459504972457259791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23755843892013259886026109 8908441459504972457259791)
          ·
            refine ⟨13362662189257458685889687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8908441459504972457259791 13362662189257458685889687)
            ·
              refine ⟨20043993283886188028834531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13362662189257458685889687 20043993283886188028834531)
              ·
                refine ⟨30065989925829282043251797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20043993283886188028834531 30065989925829282043251797)
                ·
                  refine ⟨352335819443311898944357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30065989925829282043251797 352335819443311898944357)
                  ·
                    rfl

theorem cell21_1543886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_1543886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543886 prefixEnd_1543886 := by exact prefixLift 1543886
  have htrace : WordTrace (prefixWord ++ tailWord_1543886) baseStart_1543886 baseEnd_1543886 := by
    simpa [prefixWord, tailWord_1543886, baseEnd_1543886] using wordTrace_append hprefix tailTrace_1543886
  have hstable : (prefixWord ++ tailWord_1543886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543886).length < 2 ^ (prefixWord ++ tailWord_1543886).sum := by decide
  have hdescent : baseEnd_1543886 < baseStart_1543886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543889 : List Nat := [1, 2, 2, 1, 2, 4, 3, 3, 3]
def baseStart_1543889 : Nat := 118140960795 + 1543889 * 2 ^ 59
def prefixEnd_1543889 : Nat := 4983230072969 + 3 ^ 40 * 1543889 * 2
def baseEnd_1543889 : Nat := 352336504084184560394351

theorem tailTrace_1543889 : CollatzResearch.WordTrace tailWord_1543889 prefixEnd_1543889 352336504084184560394351 := by
  unfold tailWord_1543889
  simp only [CollatzResearch.WordTrace]
  refine ⟨56310257903761303094050721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37540171935840868729367147 56310257903761303094050721)
  ·
    refine ⟨42232693427820977320538041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56310257903761303094050721 42232693427820977320538041)
    ·
      refine ⟨31674520070865732990403531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42232693427820977320538041 31674520070865732990403531)
      ·
        refine ⟨47511780106298599485605297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31674520070865732990403531 47511780106298599485605297)
        ·
          refine ⟨35633835079723949614203973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47511780106298599485605297 35633835079723949614203973)
          ·
            refine ⟨6681344077448240552663245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35633835079723949614203973 6681344077448240552663245)
            ·
              refine ⟨2505504029043090207248717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6681344077448240552663245 2505504029043090207248717)
              ·
                refine ⟨939564010891158827718269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2505504029043090207248717 939564010891158827718269)
                ·
                  refine ⟨352336504084184560394351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939564010891158827718269 352336504084184560394351)
                  ·
                    rfl

theorem cell21_1543889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 3].length) (baseStart_1543889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543889 prefixEnd_1543889 := by exact prefixLift 1543889
  have htrace : WordTrace (prefixWord ++ tailWord_1543889) baseStart_1543889 baseEnd_1543889 := by
    simpa [prefixWord, tailWord_1543889, baseEnd_1543889] using wordTrace_append hprefix tailTrace_1543889
  have hstable : (prefixWord ++ tailWord_1543889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543889).length < 2 ^ (prefixWord ++ tailWord_1543889).sum := by decide
  have hdescent : baseEnd_1543889 < baseStart_1543889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543917 : List Nat := [1, 5, 1, 2, 1, 2, 1, 8]
def baseStart_1543917 : Nat := 118140960795 + 1543917 * 2 ^ 59
def prefixEnd_1543917 : Nat := 4983230072969 + 3 ^ 40 * 1543917 * 2
def baseEnd_1543917 : Nat := 117447631355220911309209

theorem tailTrace_1543917 : CollatzResearch.WordTrace tailWord_1543917 prefixEnd_1543917 117447631355220911309209 := by
  unfold tailWord_1543917
  simp only [CollatzResearch.WordTrace]
  refine ⟨56311279147659863876070005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37540852765106575917380003 56311279147659863876070005)
  ·
    refine ⟨5279182420093112238381563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56311279147659863876070005 5279182420093112238381563)
    ·
      refine ⟨7918773630139668357572345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5279182420093112238381563 7918773630139668357572345)
      ·
        refine ⟨5939080222604751268179259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7918773630139668357572345 5939080222604751268179259)
        ·
          refine ⟨8908620333907126902268889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5939080222604751268179259 8908620333907126902268889)
          ·
            refine ⟨6681465250430345176701667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8908620333907126902268889 6681465250430345176701667)
            ·
              refine ⟨10022197875645517765052501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6681465250430345176701667 10022197875645517765052501)
              ·
                refine ⟨117447631355220911309209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10022197875645517765052501 117447631355220911309209)
                ·
                  rfl

theorem cell21_1543917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 8].length) (baseStart_1543917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1543917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1543917 prefixEnd_1543917 := by exact prefixLift 1543917
  have htrace : WordTrace (prefixWord ++ tailWord_1543917) baseStart_1543917 baseEnd_1543917 := by
    simpa [prefixWord, tailWord_1543917, baseEnd_1543917] using wordTrace_append hprefix tailTrace_1543917
  have hstable : (prefixWord ++ tailWord_1543917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543917).length < 2 ^ (prefixWord ++ tailWord_1543917).sum := by decide
  have hdescent : baseEnd_1543917 < baseStart_1543917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544013 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1544013 : Nat := 118140960795 + 1544013 * 2 ^ 59
def prefixEnd_1544013 : Nat := 4983230072969 + 3 ^ 40 * 1544013 * 2
def baseEnd_1544013 : Nat := 352364802573587900327431

theorem tailTrace_1544013 : CollatzResearch.WordTrace tailWord_1544013 prefixEnd_1544013 352364802573587900327431 := by
  unfold tailWord_1544013
  simp only [CollatzResearch.WordTrace]
  refine ⟨56314780555312072271564693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37543187036874714847709795 56314780555312072271564693)
  ·
    refine ⟨2639755338530253387729595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56314780555312072271564693 2639755338530253387729595)
    ·
      refine ⟨3959633007795380081594393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2639755338530253387729595 3959633007795380081594393)
      ·
        refine ⟨2969724755846535061195795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3959633007795380081594393 2969724755846535061195795)
        ·
          refine ⟨4454587133769802591793693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2969724755846535061195795 4454587133769802591793693)
          ·
            refine ⟨1670470175163675971922635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4454587133769802591793693 1670470175163675971922635)
            ·
              refine ⟨2505705262745513957883953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670470175163675971922635 2505705262745513957883953)
              ·
                refine ⟨1879278947059135468412965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2505705262745513957883953 1879278947059135468412965)
                ·
                  refine ⟨352364802573587900327431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1879278947059135468412965 352364802573587900327431)
                  ·
                    rfl

theorem cell21_1544013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1544013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544013 prefixEnd_1544013 := by exact prefixLift 1544013
  have htrace : WordTrace (prefixWord ++ tailWord_1544013) baseStart_1544013 baseEnd_1544013 := by
    simpa [prefixWord, tailWord_1544013, baseEnd_1544013] using wordTrace_append hprefix tailTrace_1544013
  have hstable : (prefixWord ++ tailWord_1544013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544013).length < 2 ^ (prefixWord ++ tailWord_1544013).sum := by decide
  have hdescent : baseEnd_1544013 < baseStart_1544013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544159 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 7]
def baseStart_1544159 : Nat := 118140960795 + 1544159 * 2 ^ 59
def prefixEnd_1544159 : Nat := 4983230072969 + 3 ^ 40 * 1544159 * 2
def baseEnd_1544159 : Nat := 352398121762724090893799

theorem tailTrace_1544159 : CollatzResearch.WordTrace tailWord_1544159 prefixEnd_1544159 352398121762724090893799 := by
  unfold tailWord_1544159
  simp only [CollatzResearch.WordTrace]
  refine ⟨56320105612783139206379531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37546737075188759470919687 56320105612783139206379531)
  ·
    refine ⟨84480158419174708809569297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56320105612783139206379531 84480158419174708809569297)
    ·
      refine ⟨63360118814381031607176973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84480158419174708809569297 63360118814381031607176973)
      ·
        refine ⟨23760044555392886852691365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63360118814381031607176973 23760044555392886852691365)
        ·
          refine ⟨4455008354136166284879631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23760044555392886852691365 4455008354136166284879631)
          ·
            refine ⟨6682512531204249427319447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455008354136166284879631 6682512531204249427319447)
            ·
              refine ⟨10023768796806374140979171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6682512531204249427319447 10023768796806374140979171)
              ·
                refine ⟨15035653195209561211468757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10023768796806374140979171 15035653195209561211468757)
                ·
                  refine ⟨352398121762724090893799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15035653195209561211468757 352398121762724090893799)
                  ·
                    rfl

theorem cell21_1544159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_1544159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544159 prefixEnd_1544159 := by exact prefixLift 1544159
  have htrace : WordTrace (prefixWord ++ tailWord_1544159) baseStart_1544159 baseEnd_1544159 := by
    simpa [prefixWord, tailWord_1544159, baseEnd_1544159] using wordTrace_append hprefix tailTrace_1544159
  have hstable : (prefixWord ++ tailWord_1544159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544159).length < 2 ^ (prefixWord ++ tailWord_1544159).sum := by decide
  have hdescent : baseEnd_1544159 < baseStart_1544159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544176 : List Nat := [2, 1, 1, 1, 3, 2, 3, 5, 3]
def baseStart_1544176 : Nat := 118140960795 + 1544176 * 2 ^ 59
def prefixEnd_1544176 : Nat := 4983230072969 + 3 ^ 40 * 1544176 * 2
def baseEnd_1544176 : Nat := 352402001394335839110431

theorem tailTrace_1544176 : CollatzResearch.WordTrace tailWord_1544176 prefixEnd_1544176 352402001394335839110431 := by
  unfold tailWord_1544176
  simp only [CollatzResearch.WordTrace]
  refine ⟨28160362826860775554874191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37547150435814367406498921 28160362826860775554874191)
  ·
    refine ⟨42240544240291163332311287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28160362826860775554874191 42240544240291163332311287)
    ·
      refine ⟨63360816360436744998466931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42240544240291163332311287 63360816360436744998466931)
      ·
        refine ⟨95041224540655117497700397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63360816360436744998466931 95041224540655117497700397)
        ·
          refine ⟨35640459202745669061637649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95041224540655117497700397 35640459202745669061637649)
          ·
            refine ⟨26730344402059251796228237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35640459202745669061637649 26730344402059251796228237)
            ·
              refine ⟨10023879150772219423585589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26730344402059251796228237 10023879150772219423585589)
              ·
                refine ⟨939738670384895570961149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10023879150772219423585589 939738670384895570961149)
                ·
                  refine ⟨352402001394335839110431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939738670384895570961149 352402001394335839110431)
                  ·
                    rfl

theorem cell21_1544176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 3].length) (baseStart_1544176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544176 prefixEnd_1544176 := by exact prefixLift 1544176
  have htrace : WordTrace (prefixWord ++ tailWord_1544176) baseStart_1544176 baseEnd_1544176 := by
    simpa [prefixWord, tailWord_1544176, baseEnd_1544176] using wordTrace_append hprefix tailTrace_1544176
  have hstable : (prefixWord ++ tailWord_1544176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544176).length < 2 ^ (prefixWord ++ tailWord_1544176).sum := by decide
  have hdescent : baseEnd_1544176 < baseStart_1544176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544204 : List Nat := [2, 2, 1, 2, 3, 1, 2, 8]
def baseStart_1544204 : Nat := 118140960795 + 1544204 * 2 ^ 59
def prefixEnd_1544204 : Nat := 4983230072969 + 3 ^ 40 * 1544204 * 2
def baseEnd_1544204 : Nat := 117469463791938004214569

theorem tailTrace_1544204 : CollatzResearch.WordTrace tailWord_1544204 prefixEnd_1544204 117469463791938004214569 := by
  unfold tailWord_1544204
  simp only [CollatzResearch.WordTrace]
  refine ⟨28160873448810055945883833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37547831265080074594511777 28160873448810055945883833)
  ·
    refine ⟨21120655086607541959412875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28160873448810055945883833 21120655086607541959412875)
    ·
      refine ⟨31680982629911312939119313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21120655086607541959412875 31680982629911312939119313)
      ·
        refine ⟨23760736972433484704339485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31680982629911312939119313 23760736972433484704339485)
        ·
          refine ⟨8910276364662556764127307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23760736972433484704339485 8910276364662556764127307)
          ·
            refine ⟨13365414546993835146190961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8910276364662556764127307 13365414546993835146190961)
            ·
              refine ⟨10024060910245376359643221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13365414546993835146190961 10024060910245376359643221)
              ·
                refine ⟨117469463791938004214569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10024060910245376359643221 117469463791938004214569)
                ·
                  rfl

theorem cell21_1544204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_1544204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544204 prefixEnd_1544204 := by exact prefixLift 1544204
  have htrace : WordTrace (prefixWord ++ tailWord_1544204) baseStart_1544204 baseEnd_1544204 := by
    simpa [prefixWord, tailWord_1544204, baseEnd_1544204] using wordTrace_append hprefix tailTrace_1544204
  have hstable : (prefixWord ++ tailWord_1544204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544204).length < 2 ^ (prefixWord ++ tailWord_1544204).sum := by decide
  have hdescent : baseEnd_1544204 < baseStart_1544204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544221 : List Nat := [1, 4, 2, 2, 2, 2, 1, 7]
def baseStart_1544221 : Nat := 118140960795 + 1544221 * 2 ^ 59
def prefixEnd_1544221 : Nat := 4983230072969 + 3 ^ 40 * 1544221 * 2
def baseEnd_1544221 : Nat := 117470757002475253620113

theorem tailTrace_1544221 : CollatzResearch.WordTrace tailWord_1544221 prefixEnd_1544221 117470757002475253620113 := by
  unfold tailWord_1544221
  simp only [CollatzResearch.WordTrace]
  refine ⟨56322366938558523795136517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37548244625705682530091011 56322366938558523795136517)
  ·
    refine ⟨10560443800979723211588097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56322366938558523795136517 10560443800979723211588097)
    ·
      refine ⟨7920332850734792408691073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10560443800979723211588097 7920332850734792408691073)
      ·
        refine ⟨5940249638051094306518305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7920332850734792408691073 5940249638051094306518305)
        ·
          refine ⟨4455187228538320729888729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940249638051094306518305 4455187228538320729888729)
          ·
            refine ⟨3341390421403740547416547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4455187228538320729888729 3341390421403740547416547)
            ·
              refine ⟨5012085632105610821124821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341390421403740547416547 5012085632105610821124821)
              ·
                refine ⟨117470757002475253620113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5012085632105610821124821 117470757002475253620113)
                ·
                  rfl

theorem cell21_1544221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 7].length) (baseStart_1544221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544221 prefixEnd_1544221 := by exact prefixLift 1544221
  have htrace : WordTrace (prefixWord ++ tailWord_1544221) baseStart_1544221 baseEnd_1544221 := by
    simpa [prefixWord, tailWord_1544221, baseEnd_1544221] using wordTrace_append hprefix tailTrace_1544221
  have hstable : (prefixWord ++ tailWord_1544221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544221).length < 2 ^ (prefixWord ++ tailWord_1544221).sum := by decide
  have hdescent : baseEnd_1544221 < baseStart_1544221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544280 : List Nat := [2, 1, 2, 2, 1, 4, 2, 7]
def baseStart_1544280 : Nat := 118140960795 + 1544280 * 2 ^ 59
def prefixEnd_1544280 : Nat := 4983230072969 + 3 ^ 40 * 1544280 * 2
def baseEnd_1544280 : Nat := 117475245203751589792295

theorem tailTrace_1544280 : CollatzResearch.WordTrace tailWord_1544280 prefixEnd_1544280 117475245203751589792295 := by
  unfold tailWord_1544280
  simp only [CollatzResearch.WordTrace]
  refine ⟨28162259422672388435767147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37549679230229851247689529 28162259422672388435767147)
  ·
    refine ⟨42243389134008582653650721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28162259422672388435767147 42243389134008582653650721)
    ·
      refine ⟨31682541850506436990238041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42243389134008582653650721 31682541850506436990238041)
      ·
        refine ⟨23761906387879827742678531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31682541850506436990238041 23761906387879827742678531)
        ·
          refine ⟨35642859581819741614017797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23761906387879827742678531 35642859581819741614017797)
          ·
            refine ⟨6683036171591201552628337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35642859581819741614017797 6683036171591201552628337)
            ·
              refine ⟨5012277128693401164471253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6683036171591201552628337 5012277128693401164471253)
              ·
                refine ⟨117475245203751589792295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5012277128693401164471253 117475245203751589792295)
                ·
                  rfl

theorem cell21_1544280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_1544280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544280 prefixEnd_1544280 := by exact prefixLift 1544280
  have htrace : WordTrace (prefixWord ++ tailWord_1544280) baseStart_1544280 baseEnd_1544280 := by
    simpa [prefixWord, tailWord_1544280, baseEnd_1544280] using wordTrace_append hprefix tailTrace_1544280
  have hstable : (prefixWord ++ tailWord_1544280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544280).length < 2 ^ (prefixWord ++ tailWord_1544280).sum := by decide
  have hdescent : baseEnd_1544280 < baseStart_1544280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544328 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_1544328 : Nat := 118140960795 + 1544328 * 2 ^ 59
def prefixEnd_1544328 : Nat := 4983230072969 + 3 ^ 40 * 1544328 * 2
def baseEnd_1544328 : Nat := 352436689865217352576787

theorem tailTrace_1544328 : CollatzResearch.WordTrace tailWord_1544328 prefixEnd_1544328 352436689865217352576787 := by
  unfold tailWord_1544328
  simp only [CollatzResearch.WordTrace]
  refine ⟨28163134774585440534640819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37550846366113920712854425 28163134774585440534640819)
  ·
    refine ⟨42244702161878160801961229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28163134774585440534640819 42244702161878160801961229)
    ·
      refine ⟨15841763310704310300735461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42244702161878160801961229 15841763310704310300735461)
      ·
        refine ⟨2970330620757058181387899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15841763310704310300735461 2970330620757058181387899)
        ·
          refine ⟨4455495931135587272081849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970330620757058181387899 4455495931135587272081849)
          ·
            refine ⟨3341621948351690454061387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4455495931135587272081849 3341621948351690454061387)
            ·
              refine ⟨5012432922527535681092081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341621948351690454061387 5012432922527535681092081)
              ·
                refine ⟨3759324691895651760819061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5012432922527535681092081 3759324691895651760819061)
                ·
                  refine ⟨352436689865217352576787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3759324691895651760819061 352436689865217352576787)
                  ·
                    rfl

theorem cell21_1544328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_1544328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544328 prefixEnd_1544328 := by exact prefixLift 1544328
  have htrace : WordTrace (prefixWord ++ tailWord_1544328) baseStart_1544328 baseEnd_1544328 := by
    simpa [prefixWord, tailWord_1544328, baseEnd_1544328] using wordTrace_append hprefix tailTrace_1544328
  have hstable : (prefixWord ++ tailWord_1544328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544328).length < 2 ^ (prefixWord ++ tailWord_1544328).sum := by decide
  have hdescent : baseEnd_1544328 < baseStart_1544328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544359 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 6]
def baseStart_1544359 : Nat := 118140960795 + 1544359 * 2 ^ 59
def prefixEnd_1544359 : Nat := 4983230072969 + 3 ^ 40 * 1544359 * 2
def baseEnd_1544359 : Nat := 352443764487568187560057

theorem tailTrace_1544359 : CollatzResearch.WordTrace tailWord_1544359 prefixEnd_1544359 352443764487568187560057 := by
  unfold tailWord_1544359
  simp only [CollatzResearch.WordTrace]
  refine ⟨56327400212058573363660131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37551600141372382242440087 56327400212058573363660131)
  ·
    refine ⟨84491100318087860045490197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56327400212058573363660131 84491100318087860045490197)
    ·
      refine ⟨3960520327410368439632353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84491100318087860045490197 3960520327410368439632353)
      ·
        refine ⟨2970390245557776329724265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3960520327410368439632353 2970390245557776329724265)
        ·
          refine ⟨2227792684168332247293199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2970390245557776329724265 2227792684168332247293199)
          ·
            refine ⟨3341689026252498370939799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227792684168332247293199 3341689026252498370939799)
            ·
              refine ⟨5012533539378747556409699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341689026252498370939799 5012533539378747556409699)
              ·
                refine ⟨7518800309068121334614549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012533539378747556409699 7518800309068121334614549)
                ·
                  refine ⟨352443764487568187560057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7518800309068121334614549 352443764487568187560057)
                  ·
                    rfl

theorem cell21_1544359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 6].length) (baseStart_1544359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544359 prefixEnd_1544359 := by exact prefixLift 1544359
  have htrace : WordTrace (prefixWord ++ tailWord_1544359) baseStart_1544359 baseEnd_1544359 := by
    simpa [prefixWord, tailWord_1544359, baseEnd_1544359] using wordTrace_append hprefix tailTrace_1544359
  have hstable : (prefixWord ++ tailWord_1544359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544359).length < 2 ^ (prefixWord ++ tailWord_1544359).sum := by decide
  have hdescent : baseEnd_1544359 < baseStart_1544359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544401 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 6]
def baseStart_1544401 : Nat := 118140960795 + 1544401 * 2 ^ 59
def prefixEnd_1544401 : Nat := 4983230072969 + 3 ^ 40 * 1544401 * 2
def baseEnd_1544401 : Nat := 352453349459785447859971

theorem tailTrace_1544401 : CollatzResearch.WordTrace tailWord_1544401 prefixEnd_1544401 352453349459785447859971 := by
  unfold tailWord_1544401
  simp only [CollatzResearch.WordTrace]
  refine ⟨56328932077906414536689057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37552621385270943024459371 56328932077906414536689057)
  ·
    refine ⟨42246699058429810902516793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56328932077906414536689057 42246699058429810902516793)
    ·
      refine ⟨31685024293822358176887595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42246699058429810902516793 31685024293822358176887595)
      ·
        refine ⟨47527536440733537265331393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31685024293822358176887595 47527536440733537265331393)
        ·
          refine ⟨35645652330550152948998545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47527536440733537265331393 35645652330550152948998545)
          ·
            refine ⟨26734239247912614711748909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35645652330550152948998545 26734239247912614711748909)
            ·
              refine ⟨10025339717967230516905841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26734239247912614711748909 10025339717967230516905841)
              ·
                refine ⟨7519004788475422887679381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10025339717967230516905841 7519004788475422887679381)
                ·
                  refine ⟨352453349459785447859971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7519004788475422887679381 352453349459785447859971)
                  ·
                    rfl

theorem cell21_1544401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_1544401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544401 prefixEnd_1544401 := by exact prefixLift 1544401
  have htrace : WordTrace (prefixWord ++ tailWord_1544401) baseStart_1544401 baseEnd_1544401 := by
    simpa [prefixWord, tailWord_1544401, baseEnd_1544401] using wordTrace_append hprefix tailTrace_1544401
  have hstable : (prefixWord ++ tailWord_1544401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544401).length < 2 ^ (prefixWord ++ tailWord_1544401).sum := by decide
  have hdescent : baseEnd_1544401 < baseStart_1544401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544573 : List Nat := [1, 4, 1, 1, 2, 5, 1, 3, 3]
def baseStart_1544573 : Nat := 118140960795 + 1544573 * 2 ^ 59
def prefixEnd_1544573 : Nat := 4983230072969 + 3 ^ 40 * 1544573 * 2
def baseEnd_1544573 : Nat := 352492602203151370992953

theorem tailTrace_1544573 : CollatzResearch.WordTrace tailWord_1544573 prefixEnd_1544573 352492602203151370992953 := by
  unfold tailWord_1544573
  simp only [CollatzResearch.WordTrace]
  refine ⟨56335205433283287911950373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37556803622188858607966915 56335205433283287911950373)
  ·
    refine ⟨10562851018740616483490695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56335205433283287911950373 10562851018740616483490695)
    ·
      refine ⟨15844276528110924725236043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10562851018740616483490695 15844276528110924725236043)
      ·
        refine ⟨23766414792166387087854065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15844276528110924725236043 23766414792166387087854065)
        ·
          refine ⟨17824811094124790315890549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23766414792166387087854065 17824811094124790315890549)
          ·
            refine ⟨1671076040074199092114739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17824811094124790315890549 1671076040074199092114739)
            ·
              refine ⟨2506614060111298638172109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671076040074199092114739 2506614060111298638172109)
              ·
                refine ⟨939980272541736989314541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2506614060111298638172109 939980272541736989314541)
                ·
                  refine ⟨352492602203151370992953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939980272541736989314541 352492602203151370992953)
                  ·
                    rfl

theorem cell21_1544573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_1544573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544573 prefixEnd_1544573 := by exact prefixLift 1544573
  have htrace : WordTrace (prefixWord ++ tailWord_1544573) baseStart_1544573 baseEnd_1544573 := by
    simpa [prefixWord, tailWord_1544573, baseEnd_1544573] using wordTrace_append hprefix tailTrace_1544573
  have hstable : (prefixWord ++ tailWord_1544573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544573).length < 2 ^ (prefixWord ++ tailWord_1544573).sum := by decide
  have hdescent : baseEnd_1544573 < baseStart_1544573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544590 : List Nat := [4, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_1544590 : Nat := 118140960795 + 1544590 * 2 ^ 59
def prefixEnd_1544590 : Nat := 4983230072969 + 3 ^ 40 * 1544590 * 2
def baseEnd_1544590 : Nat := 352496481834763119209585

theorem tailTrace_1544590 : CollatzResearch.WordTrace tailWord_1544590 prefixEnd_1544590 352496481834763119209585 := by
  unfold tailWord_1544590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7041978184277712476914903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37557216982814466543546149 7041978184277712476914903)
  ·
    refine ⟨10562967276416568715372355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7041978184277712476914903 10562967276416568715372355)
    ·
      refine ⟨15844450914624853073058533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10562967276416568715372355 15844450914624853073058533)
      ·
        refine ⟨2970834546492159951198475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15844450914624853073058533 2970834546492159951198475)
        ·
          refine ⟨4456251819738239926797713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970834546492159951198475 4456251819738239926797713)
          ·
            refine ⟨3342188864803679945098285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4456251819738239926797713 3342188864803679945098285)
            ·
              refine ⟨1253320824301379979411857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3342188864803679945098285 1253320824301379979411857)
              ·
                refine ⟨939990618226034984558893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1253320824301379979411857 939990618226034984558893)
                ·
                  refine ⟨352496481834763119209585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939990618226034984558893 352496481834763119209585)
                  ·
                    rfl

theorem cell21_1544590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_1544590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544590 prefixEnd_1544590 := by exact prefixLift 1544590
  have htrace : WordTrace (prefixWord ++ tailWord_1544590) baseStart_1544590 baseEnd_1544590 := by
    simpa [prefixWord, tailWord_1544590, baseEnd_1544590] using wordTrace_append hprefix tailTrace_1544590
  have hstable : (prefixWord ++ tailWord_1544590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544590).length < 2 ^ (prefixWord ++ tailWord_1544590).sum := by decide
  have hdescent : baseEnd_1544590 < baseStart_1544590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544641 : List Nat := [1, 2, 7, 1, 2, 1, 2, 2, 3]
def baseStart_1544641 : Nat := 118140960795 + 1544641 * 2 ^ 59
def prefixEnd_1544641 : Nat := 4983230072969 + 3 ^ 40 * 1544641 * 2
def baseEnd_1544641 : Nat := 352508120729598363859481

theorem tailTrace_1544641 : CollatzResearch.WordTrace tailWord_1544641 prefixEnd_1544641 352508120729598363859481 := by
  unfold tailWord_1544641
  simp only [CollatzResearch.WordTrace]
  refine ⟨56337685597036935525425777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37558457064691290350283851 56337685597036935525425777)
  ·
    refine ⟨42253264197777701644069333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56337685597036935525425777 42253264197777701644069333)
    ·
      refine ⟨990310879635414882282875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42253264197777701644069333 990310879635414882282875)
      ·
        refine ⟨1485466319453122323424313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990310879635414882282875 1485466319453122323424313)
        ·
          refine ⟨1114099739589841742568235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1485466319453122323424313 1114099739589841742568235)
          ·
            refine ⟨1671149609384762613852353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114099739589841742568235 1671149609384762613852353)
            ·
              refine ⟨1253362207038571960389265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1671149609384762613852353 1253362207038571960389265)
              ·
                refine ⟨940021655278928970291949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1253362207038571960389265 940021655278928970291949)
                ·
                  refine ⟨352508120729598363859481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940021655278928970291949 352508120729598363859481)
                  ·
                    rfl

theorem cell21_1544641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 3].length) (baseStart_1544641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544641 prefixEnd_1544641 := by exact prefixLift 1544641
  have htrace : WordTrace (prefixWord ++ tailWord_1544641) baseStart_1544641 baseEnd_1544641 := by
    simpa [prefixWord, tailWord_1544641, baseEnd_1544641] using wordTrace_append hprefix tailTrace_1544641
  have hstable : (prefixWord ++ tailWord_1544641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544641).length < 2 ^ (prefixWord ++ tailWord_1544641).sum := by decide
  have hdescent : baseEnd_1544641 < baseStart_1544641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544708 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_1544708 : Nat := 118140960795 + 1544708 * 2 ^ 59
def prefixEnd_1544708 : Nat := 4983230072969 + 3 ^ 40 * 1544708 * 2
def baseEnd_1544708 : Nat := 352523411042421136242677

theorem tailTrace_1544708 : CollatzResearch.WordTrace tailWord_1544708 prefixEnd_1544708 352523411042421136242677 := by
  unfold tailWord_1544708
  simp only [CollatzResearch.WordTrace]
  refine ⟨28170064643897102984057389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37560086191862803978743185 28170064643897102984057389)
  ·
    refine ⟨10563774241461413619021521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28170064643897102984057389 10563774241461413619021521)
    ·
      refine ⟨7922830681096060214266141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10563774241461413619021521 7922830681096060214266141)
      ·
        refine ⟨2971061505411022580349803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7922830681096060214266141 2971061505411022580349803)
        ·
          refine ⟨4456592258116533870524705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971061505411022580349803 4456592258116533870524705)
          ·
            refine ⟨3342444193587400402893529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4456592258116533870524705 3342444193587400402893529)
            ·
              refine ⟨2506833145190550302170147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3342444193587400402893529 2506833145190550302170147)
              ·
                refine ⟨3760249717785825453255221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506833145190550302170147 3760249717785825453255221)
                ·
                  refine ⟨352523411042421136242677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3760249717785825453255221 352523411042421136242677)
                  ·
                    rfl

theorem cell21_1544708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_1544708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544708 prefixEnd_1544708 := by exact prefixLift 1544708
  have htrace : WordTrace (prefixWord ++ tailWord_1544708) baseStart_1544708 baseEnd_1544708 := by
    simpa [prefixWord, tailWord_1544708, baseEnd_1544708] using wordTrace_append hprefix tailTrace_1544708
  have hstable : (prefixWord ++ tailWord_1544708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544708).length < 2 ^ (prefixWord ++ tailWord_1544708).sum := by decide
  have hdescent : baseEnd_1544708 < baseStart_1544708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544818 : List Nat := [3, 2, 1, 2, 4, 2, 2, 2, 3]
def baseStart_1544818 : Nat := 118140960795 + 1544818 * 2 ^ 59
def prefixEnd_1544818 : Nat := 4983230072969 + 3 ^ 40 * 1544818 * 2
def baseEnd_1544818 : Nat := 352548514541085389409119

theorem tailTrace_1544818 : CollatzResearch.WordTrace tailWord_1544818 prefixEnd_1544818 352548514541085389409119 := by
  unfold tailWord_1544818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14086035329348923688654777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37562760878263796503079405 14086035329348923688654777)
  ·
    refine ⟨10564526497011692766491083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14086035329348923688654777 10564526497011692766491083)
    ·
      refine ⟨15846789745517539149736625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10564526497011692766491083 15846789745517539149736625)
      ·
        refine ⟨11885092309138154362302469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15846789745517539149736625 11885092309138154362302469)
        ·
          refine ⟨2228454807963403942931713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11885092309138154362302469 2228454807963403942931713)
          ·
            refine ⟨1671341105972552957198785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2228454807963403942931713 1671341105972552957198785)
            ·
              refine ⟨1253505829479414717899089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1671341105972552957198785 1253505829479414717899089)
              ·
                refine ⟨940129372109561038424317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1253505829479414717899089 940129372109561038424317)
                ·
                  refine ⟨352548514541085389409119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940129372109561038424317 352548514541085389409119)
                  ·
                    rfl

theorem cell21_1544818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_1544818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544818 prefixEnd_1544818 := by exact prefixLift 1544818
  have htrace : WordTrace (prefixWord ++ tailWord_1544818) baseStart_1544818 baseEnd_1544818 := by
    simpa [prefixWord, tailWord_1544818, baseEnd_1544818] using wordTrace_append hprefix tailTrace_1544818
  have hstable : (prefixWord ++ tailWord_1544818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544818).length < 2 ^ (prefixWord ++ tailWord_1544818).sum := by decide
  have hdescent : baseEnd_1544818 < baseStart_1544818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544829 : List Nat := [1, 4, 1, 1, 5, 2, 1, 6]
def baseStart_1544829 : Nat := 118140960795 + 1544829 * 2 ^ 59
def prefixEnd_1544829 : Nat := 4983230072969 + 3 ^ 40 * 1544829 * 2
def baseEnd_1544829 : Nat := 117517008296983938241921

theorem tailTrace_1544829 : CollatzResearch.WordTrace tailWord_1544829 prefixEnd_1544829 117517008296983938241921 := by
  unfold tailWord_1544829
  simp only [CollatzResearch.WordTrace]
  refine ⟨56344542520355843633269541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37563028346903895755513027 56344542520355843633269541)
  ·
    refine ⟨10564601722566720681238039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56344542520355843633269541 10564601722566720681238039)
    ·
      refine ⟨15846902583850081021857059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10564601722566720681238039 15846902583850081021857059)
      ·
        refine ⟨23770353875775121532785589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15846902583850081021857059 23770353875775121532785589)
        ·
          refine ⟨2228470675853917643698649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23770353875775121532785589 2228470675853917643698649)
          ·
            refine ⟨1671353006890438232773987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2228470675853917643698649 1671353006890438232773987)
            ·
              refine ⟨2507029510335657349160981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671353006890438232773987 2507029510335657349160981)
              ·
                refine ⟨117517008296983938241921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2507029510335657349160981 117517008296983938241921)
                ·
                  rfl

theorem cell21_1544829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 6].length) (baseStart_1544829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544829 prefixEnd_1544829 := by exact prefixLift 1544829
  have htrace : WordTrace (prefixWord ++ tailWord_1544829) baseStart_1544829 baseEnd_1544829 := by
    simpa [prefixWord, tailWord_1544829, baseEnd_1544829] using wordTrace_append hprefix tailTrace_1544829
  have hstable : (prefixWord ++ tailWord_1544829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544829).length < 2 ^ (prefixWord ++ tailWord_1544829).sum := by decide
  have hdescent : baseEnd_1544829 < baseStart_1544829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544860 : List Nat := [2, 2, 3, 2, 2, 1, 1, 5, 3]
def baseStart_1544860 : Nat := 118140960795 + 1544860 * 2 ^ 59
def prefixEnd_1544860 : Nat := 4983230072969 + 3 ^ 40 * 1544860 * 2
def baseEnd_1544860 : Nat := 352558099513302649709033

theorem tailTrace_1544860 : CollatzResearch.WordTrace tailWord_1544860 prefixEnd_1544860 352558099513302649709033 := by
  unfold tailWord_1544860
  simp only [CollatzResearch.WordTrace]
  refine ⟨28172836591621767963824017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37563782122162357285098689 28172836591621767963824017)
  ·
    refine ⟨21129627443716325972868013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28172836591621767963824017 21129627443716325972868013)
    ·
      refine ⟨7923610291393622239825505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21129627443716325972868013 7923610291393622239825505)
      ·
        refine ⟨5942707718545216679869129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7923610291393622239825505 5942707718545216679869129)
        ·
          refine ⟨4457030788908912509901847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5942707718545216679869129 4457030788908912509901847)
          ·
            refine ⟨6685546183363368764852771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457030788908912509901847 6685546183363368764852771)
            ·
              refine ⟨10028319275045053147279157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6685546183363368764852771 10028319275045053147279157)
              ·
                refine ⟨940154932035473732557421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10028319275045053147279157 940154932035473732557421)
                ·
                  refine ⟨352558099513302649709033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940154932035473732557421 352558099513302649709033)
                  ·
                    rfl

theorem cell21_1544860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_1544860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544860 prefixEnd_1544860 := by exact prefixLift 1544860
  have htrace : WordTrace (prefixWord ++ tailWord_1544860) baseStart_1544860 baseEnd_1544860 := by
    simpa [prefixWord, tailWord_1544860, baseEnd_1544860] using wordTrace_append hprefix tailTrace_1544860
  have hstable : (prefixWord ++ tailWord_1544860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544860).length < 2 ^ (prefixWord ++ tailWord_1544860).sum := by decide
  have hdescent : baseEnd_1544860 < baseStart_1544860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544933 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 6]
def baseStart_1544933 : Nat := 118140960795 + 1544933 * 2 ^ 59
def prefixEnd_1544933 : Nat := 4983230072969 + 3 ^ 40 * 1544933 * 2
def baseEnd_1544933 : Nat := 352574759107870744992217

theorem tailTrace_1544933 : CollatzResearch.WordTrace tailWord_1544933 prefixEnd_1544933 352574759107870744992217 := by
  unfold tailWord_1544933
  simp only [CollatzResearch.WordTrace]
  refine ⟨56348335711979069395055453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37565557141319379596703635 56348335711979069395055453)
  ·
    refine ⟨21130625891992151023145795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56348335711979069395055453 21130625891992151023145795)
    ·
      refine ⟨31695938837988226534718693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21130625891992151023145795 31695938837988226534718693)
      ·
        refine ⟨5942988532122792475259755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31695938837988226534718693 5942988532122792475259755)
        ·
          refine ⟨8914482798184188712889633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5942988532122792475259755 8914482798184188712889633)
          ·
            refine ⟨6685862098638141534667225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8914482798184188712889633 6685862098638141534667225)
            ·
              refine ⟨5014396573978606151000419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6685862098638141534667225 5014396573978606151000419)
              ·
                refine ⟨7521594860967909226500629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014396573978606151000419 7521594860967909226500629)
                ·
                  refine ⟨352574759107870744992217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7521594860967909226500629 352574759107870744992217)
                  ·
                    rfl

theorem cell21_1544933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_1544933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544933 prefixEnd_1544933 := by exact prefixLift 1544933
  have htrace : WordTrace (prefixWord ++ tailWord_1544933) baseStart_1544933 baseEnd_1544933 := by
    simpa [prefixWord, tailWord_1544933, baseEnd_1544933] using wordTrace_append hprefix tailTrace_1544933
  have hstable : (prefixWord ++ tailWord_1544933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544933).length < 2 ^ (prefixWord ++ tailWord_1544933).sum := by decide
  have hdescent : baseEnd_1544933 < baseStart_1544933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544936 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 5]
def baseStart_1544936 : Nat := 118140960795 + 1544936 * 2 ^ 59
def prefixEnd_1544936 : Nat := 4983230072969 + 3 ^ 40 * 1544936 * 2
def baseEnd_1544936 : Nat := 352575443748743406442211

theorem tailTrace_1544936 : CollatzResearch.WordTrace tailWord_1544936 prefixEnd_1544936 352575443748743406442211 := by
  unfold tailWord_1544936
  simp only [CollatzResearch.WordTrace]
  refine ⟨28174222565484100453707331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37565630087312133938276441 28174222565484100453707331)
  ·
    refine ⟨42261333848226150680560997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28174222565484100453707331 42261333848226150680560997)
    ·
      refine ⟨7924000096542403252605187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42261333848226150680560997 7924000096542403252605187)
      ·
        refine ⟨11886000144813604878907781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7924000096542403252605187 11886000144813604878907781)
        ·
          refine ⟨2228625027152550914795209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11886000144813604878907781 2228625027152550914795209)
          ·
            refine ⟨1671468770364413186096407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2228625027152550914795209 1671468770364413186096407)
            ·
              refine ⟨2507203155546619779144611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671468770364413186096407 2507203155546619779144611)
              ·
                refine ⟨3760804733319929668716917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507203155546619779144611 3760804733319929668716917)
                ·
                  refine ⟨352575443748743406442211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3760804733319929668716917 352575443748743406442211)
                  ·
                    rfl

theorem cell21_1544936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_1544936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544936 prefixEnd_1544936 := by exact prefixLift 1544936
  have htrace : WordTrace (prefixWord ++ tailWord_1544936) baseStart_1544936 baseEnd_1544936 := by
    simpa [prefixWord, tailWord_1544936, baseEnd_1544936] using wordTrace_append hprefix tailTrace_1544936
  have hstable : (prefixWord ++ tailWord_1544936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544936).length < 2 ^ (prefixWord ++ tailWord_1544936).sum := by decide
  have hdescent : baseEnd_1544936 < baseStart_1544936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544950 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1544950 : Nat := 118140960795 + 1544950 * 2 ^ 59
def prefixEnd_1544950 : Nat := 4983230072969 + 3 ^ 40 * 1544950 * 2
def baseEnd_1544950 : Nat := 352578638739482493208849

theorem tailTrace_1544950 : CollatzResearch.WordTrace tailWord_1544950 prefixEnd_1544950 352578638739482493208849 := by
  unfold tailWord_1544950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521809734557342581151519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37565970501944987532282869 3521809734557342581151519)
  ·
    refine ⟨5282714601836013871727279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3521809734557342581151519 5282714601836013871727279)
    ·
      refine ⟨7924071902754020807590919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5282714601836013871727279 7924071902754020807590919)
      ·
        refine ⟨11886107854131031211386379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7924071902754020807590919 11886107854131031211386379)
        ·
          refine ⟨17829161781196546817079569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11886107854131031211386379 17829161781196546817079569)
          ·
            refine ⟨13371871335897410112809677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17829161781196546817079569 13371871335897410112809677)
            ·
              refine ⟨5014451750961528792303629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13371871335897410112809677 5014451750961528792303629)
              ·
                refine ⟨1880419406610573297113861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5014451750961528792303629 1880419406610573297113861)
                ·
                  refine ⟨352578638739482493208849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1880419406610573297113861 352578638739482493208849)
                  ·
                    rfl

theorem cell21_1544950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1544950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1544950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1544950 prefixEnd_1544950 := by exact prefixLift 1544950
  have htrace : WordTrace (prefixWord ++ tailWord_1544950) baseStart_1544950 baseEnd_1544950 := by
    simpa [prefixWord, tailWord_1544950, baseEnd_1544950] using wordTrace_append hprefix tailTrace_1544950
  have hstable : (prefixWord ++ tailWord_1544950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544950).length < 2 ^ (prefixWord ++ tailWord_1544950).sum := by decide
  have hdescent : baseEnd_1544950 < baseStart_1544950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545009 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 4]
def baseStart_1545009 : Nat := 118140960795 + 1545009 * 2 ^ 59
def prefixEnd_1545009 : Nat := 4983230072969 + 3 ^ 40 * 1545009 * 2
def baseEnd_1545009 : Nat := 352592103343311501725395

theorem tailTrace_1545009 : CollatzResearch.WordTrace tailWord_1545009 prefixEnd_1545009 352592103343311501725395 := by
  unfold tailWord_1545009
  simp only [CollatzResearch.WordTrace]
  refine ⟨56351107659703734374822081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37567405106469156249881387 56351107659703734374822081)
  ·
    refine ⟨42263330744777800781116561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56351107659703734374822081 42263330744777800781116561)
    ·
      refine ⟨31697498058583350585837421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42263330744777800781116561 31697498058583350585837421)
      ·
        refine ⟨11886561771968756469689033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31697498058583350585837421 11886561771968756469689033)
        ·
          refine ⟨8914921328976567352266775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11886561771968756469689033 8914921328976567352266775)
          ·
            refine ⟨13372381993464851028400163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8914921328976567352266775 13372381993464851028400163)
            ·
              refine ⟨20058572990197276542600245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13372381993464851028400163 20058572990197276542600245)
              ·
                refine ⟨1880491217830994675868773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20058572990197276542600245 1880491217830994675868773)
                ·
                  refine ⟨352592103343311501725395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1880491217830994675868773 352592103343311501725395)
                  ·
                    rfl

theorem cell21_1545009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_1545009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545009 prefixEnd_1545009 := by exact prefixLift 1545009
  have htrace : WordTrace (prefixWord ++ tailWord_1545009) baseStart_1545009 baseEnd_1545009 := by
    simpa [prefixWord, tailWord_1545009, baseEnd_1545009] using wordTrace_append hprefix tailTrace_1545009
  have hstable : (prefixWord ++ tailWord_1545009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545009).length < 2 ^ (prefixWord ++ tailWord_1545009).sum := by decide
  have hdescent : baseEnd_1545009 < baseStart_1545009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545012 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1545012 : Nat := 118140960795 + 1545012 * 2 ^ 59
def prefixEnd_1545012 : Nat := 4983230072969 + 3 ^ 40 * 1545012 * 2
def baseEnd_1545012 : Nat := 352592787984184163175389

theorem tailTrace_1545012 : CollatzResearch.WordTrace tailWord_1545012 prefixEnd_1545012 352592787984184163175389 := by
  unfold tailWord_1545012
  simp only [CollatzResearch.WordTrace]
  refine ⟨28175608539346432943590645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37567478052461910591454193 28175608539346432943590645)
  ·
    refine ⟨2641463300563728088461623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28175608539346432943590645 2641463300563728088461623)
    ·
      refine ⟨3962194950845592132692435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2641463300563728088461623 3962194950845592132692435)
      ·
        refine ⟨5943292426268388199038653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3962194950845592132692435 5943292426268388199038653)
        ·
          refine ⟨2228734659850645574639495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5943292426268388199038653 2228734659850645574639495)
          ·
            refine ⟨3343101989775968361959243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2228734659850645574639495 3343101989775968361959243)
            ·
              refine ⟨5014652984663952542938865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343101989775968361959243 5014652984663952542938865)
              ·
                refine ⟨3760989738497964407204149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5014652984663952542938865 3760989738497964407204149)
                ·
                  refine ⟨352592787984184163175389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3760989738497964407204149 352592787984184163175389)
                  ·
                    rfl

theorem cell21_1545012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1545012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545012 prefixEnd_1545012 := by exact prefixLift 1545012
  have htrace : WordTrace (prefixWord ++ tailWord_1545012) baseStart_1545012 baseEnd_1545012 := by
    simpa [prefixWord, tailWord_1545012, baseEnd_1545012] using wordTrace_append hprefix tailTrace_1545012
  have hstable : (prefixWord ++ tailWord_1545012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545012).length < 2 ^ (prefixWord ++ tailWord_1545012).sum := by decide
  have hdescent : baseEnd_1545012 < baseStart_1545012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545119 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 4]
def baseStart_1545119 : Nat := 118140960795 + 1545119 * 2 ^ 59
def prefixEnd_1545119 : Nat := 4983230072969 + 3 ^ 40 * 1545119 * 2
def baseEnd_1545119 : Nat := 352617206841975754891837

theorem tailTrace_1545119 : CollatzResearch.WordTrace tailWord_1545119 prefixEnd_1545119 352617206841975754891837 := by
  unfold tailWord_1545119
  simp only [CollatzResearch.WordTrace]
  refine ⟨56355119689305223161326411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37570079792870148774217607 56355119689305223161326411)
  ·
    refine ⟨84532679533957834741989617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56355119689305223161326411 84532679533957834741989617)
    ·
      refine ⟨63399509650468376056492213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84532679533957834741989617 63399509650468376056492213)
      ·
        refine ⟨5943704029731410255296145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63399509650468376056492213 5943704029731410255296145)
        ·
          refine ⟨4457778022298557691472109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5943704029731410255296145 4457778022298557691472109)
          ·
            refine ⟨1671666758361959134302041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4457778022298557691472109 1671666758361959134302041)
            ·
              refine ⟨1253750068771469350726531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1671666758361959134302041 1253750068771469350726531)
              ·
                refine ⟨1880625103157204026089797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253750068771469350726531 1880625103157204026089797)
                ·
                  refine ⟨352617206841975754891837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1880625103157204026089797 352617206841975754891837)
                  ·
                    rfl

theorem cell21_1545119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 4].length) (baseStart_1545119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545119 prefixEnd_1545119 := by exact prefixLift 1545119
  have htrace : WordTrace (prefixWord ++ tailWord_1545119) baseStart_1545119 baseEnd_1545119 := by
    simpa [prefixWord, tailWord_1545119, baseEnd_1545119] using wordTrace_append hprefix tailTrace_1545119
  have hstable : (prefixWord ++ tailWord_1545119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545119).length < 2 ^ (prefixWord ++ tailWord_1545119).sum := by decide
  have hdescent : baseEnd_1545119 < baseStart_1545119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545223 : List Nat := [1, 1, 4, 3, 1, 1, 1, 6, 3]
def baseStart_1545223 : Nat := 118140960795 + 1545223 * 2 ^ 59
def prefixEnd_1545223 : Nat := 4983230072969 + 3 ^ 40 * 1545223 * 2
def baseEnd_1545223 : Nat := 352640941058894685158291

theorem tailTrace_1545223 : CollatzResearch.WordTrace tailWord_1545223 prefixEnd_1545223 352640941058894685158291 := by
  unfold tailWord_1545223
  simp only [CollatzResearch.WordTrace]
  refine ⟨56358912880928448923112323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37572608587285632615408215 56358912880928448923112323)
  ·
    refine ⟨84538369321392673384668485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56358912880928448923112323 84538369321392673384668485)
    ·
      refine ⟨15850944247761126259625341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84538369321392673384668485 15850944247761126259625341)
      ·
        refine ⟨5944104092910422347359503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15850944247761126259625341 5944104092910422347359503)
        ·
          refine ⟨8916156139365633521039255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5944104092910422347359503 8916156139365633521039255)
          ·
            refine ⟨13374234209048450281558883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8916156139365633521039255 13374234209048450281558883)
            ·
              refine ⟨20061351313572675422338325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13374234209048450281558883 20061351313572675422338325)
              ·
                refine ⟨940375842823719160422109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20061351313572675422338325 940375842823719160422109)
                ·
                  refine ⟨352640941058894685158291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940375842823719160422109 352640941058894685158291)
                  ·
                    rfl

theorem cell21_1545223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 3].length) (baseStart_1545223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545223 prefixEnd_1545223 := by exact prefixLift 1545223
  have htrace : WordTrace (prefixWord ++ tailWord_1545223) baseStart_1545223 baseEnd_1545223 := by
    simpa [prefixWord, tailWord_1545223, baseEnd_1545223] using wordTrace_append hprefix tailTrace_1545223
  have hstable : (prefixWord ++ tailWord_1545223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545223).length < 2 ^ (prefixWord ++ tailWord_1545223).sum := by decide
  have hdescent : baseEnd_1545223 < baseStart_1545223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545251 : List Nat := [1, 1, 1, 4, 3, 3, 1, 7]
def baseStart_1545251 : Nat := 118140960795 + 1545251 * 2 ^ 59
def prefixEnd_1545251 : Nat := 4983230072969 + 3 ^ 40 * 1545251 * 2
def baseEnd_1545251 : Nat := 117549110346790952897189

theorem tailTrace_1545251 : CollatzResearch.WordTrace tailWord_1545251 prefixEnd_1545251 117549110346790952897189 := by
  unfold tailWord_1545251
  simp only [CollatzResearch.WordTrace]
  refine ⟨56359934124827009705131607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37573289416551339803421071 56359934124827009705131607)
  ·
    refine ⟨84539901187240514557697411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56359934124827009705131607 84539901187240514557697411)
    ·
      refine ⟨126809851780860771836546117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84539901187240514557697411 126809851780860771836546117)
      ·
        refine ⟨23776847208911394719352397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126809851780860771836546117 23776847208911394719352397)
        ·
          refine ⟨8916317703341773019757149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23776847208911394719352397 8916317703341773019757149)
          ·
            refine ⟨3343619138753164882408931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8916317703341773019757149 3343619138753164882408931)
            ·
              refine ⟨5015428708129747323613397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343619138753164882408931 5015428708129747323613397)
              ·
                refine ⟨117549110346790952897189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5015428708129747323613397 117549110346790952897189)
                ·
                  rfl

theorem cell21_1545251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 7].length) (baseStart_1545251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545251 prefixEnd_1545251 := by exact prefixLift 1545251
  have htrace : WordTrace (prefixWord ++ tailWord_1545251) baseStart_1545251 baseEnd_1545251 := by
    simpa [prefixWord, tailWord_1545251, baseEnd_1545251] using wordTrace_append hprefix tailTrace_1545251
  have hstable : (prefixWord ++ tailWord_1545251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545251).length < 2 ^ (prefixWord ++ tailWord_1545251).sum := by decide
  have hdescent : baseEnd_1545251 < baseStart_1545251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545268 : List Nat := [2, 5, 1, 2, 1, 1, 9]
def baseStart_1545268 : Nat := 118140960795 + 1545268 * 2 ^ 59
def prefixEnd_1545268 : Nat := 4983230072969 + 3 ^ 40 * 1545268 * 2
def baseEnd_1545268 : Nat := 39183467852442734100911

theorem tailTrace_1545268 : CollatzResearch.WordTrace tailWord_1545268 prefixEnd_1545268 39183467852442734100911 := by
  unfold tailWord_1545268
  simp only [CollatzResearch.WordTrace]
  refine ⟨28180277082882710804250229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37573702777176947739000305 28180277082882710804250229)
  ·
    refine ⟨2641900976520254137898459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28180277082882710804250229 2641900976520254137898459)
    ·
      refine ⟨3962851464780381206847689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2641900976520254137898459 3962851464780381206847689)
      ·
        refine ⟨2972138598585285905135767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3962851464780381206847689 2972138598585285905135767)
        ·
          refine ⟨4458207897877928857703651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2972138598585285905135767 4458207897877928857703651)
          ·
            refine ⟨6687311846816893286555477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4458207897877928857703651 6687311846816893286555477)
            ·
              refine ⟨39183467852442734100911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6687311846816893286555477 39183467852442734100911)
              ·
                rfl

theorem cell21_1545268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 9].length) (baseStart_1545268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545268 prefixEnd_1545268 := by exact prefixLift 1545268
  have htrace : WordTrace (prefixWord ++ tailWord_1545268) baseStart_1545268 baseEnd_1545268 := by
    simpa [prefixWord, tailWord_1545268, baseEnd_1545268] using wordTrace_append hprefix tailTrace_1545268
  have hstable : (prefixWord ++ tailWord_1545268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545268).length < 2 ^ (prefixWord ++ tailWord_1545268).sum := by decide
  have hdescent : baseEnd_1545268 < baseStart_1545268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545333 : List Nat := [1, 3, 4, 3, 1, 1, 1, 4, 3]
def baseStart_1545333 : Nat := 118140960795 + 1545333 * 2 ^ 59
def prefixEnd_1545333 : Nat := 4983230072969 + 3 ^ 40 * 1545333 * 2
def baseEnd_1545333 : Nat := 352666044557558938324733

theorem tailTrace_1545333 : CollatzResearch.WordTrace tailWord_1545333 prefixEnd_1545333 352666044557558938324733 := by
  unfold tailWord_1545333
  simp only [CollatzResearch.WordTrace]
  refine ⟨56362924910529937709616653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37575283273686625139744435 56362924910529937709616653)
  ·
    refine ⟨21136096841448726641106245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56362924910529937709616653 21136096841448726641106245)
    ·
      refine ⟨3963018157771636245207421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21136096841448726641106245 3963018157771636245207421)
      ·
        refine ⟨1486131809164363591952783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3963018157771636245207421 1486131809164363591952783)
        ·
          refine ⟨2229197713746545387929175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486131809164363591952783 2229197713746545387929175)
          ·
            refine ⟨3343796570619818081893763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229197713746545387929175 3343796570619818081893763)
            ·
              refine ⟨5015694855929727122840645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343796570619818081893763 5015694855929727122840645)
              ·
                refine ⟨940442785486823835532621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5015694855929727122840645 940442785486823835532621)
                ·
                  refine ⟨352666044557558938324733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940442785486823835532621 352666044557558938324733)
                  ·
                    rfl

theorem cell21_1545333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_1545333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545333 prefixEnd_1545333 := by exact prefixLift 1545333
  have htrace : WordTrace (prefixWord ++ tailWord_1545333) baseStart_1545333 baseEnd_1545333 := by
    simpa [prefixWord, tailWord_1545333, baseEnd_1545333] using wordTrace_append hprefix tailTrace_1545333
  have hstable : (prefixWord ++ tailWord_1545333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545333).length < 2 ^ (prefixWord ++ tailWord_1545333).sum := by decide
  have hdescent : baseEnd_1545333 < baseStart_1545333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545358 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1545358 : Nat := 118140960795 + 1545358 * 2 ^ 59
def prefixEnd_1545358 : Nat := 4983230072969 + 3 ^ 40 * 1545358 * 2
def baseEnd_1545358 : Nat := 352671749898164450408015

theorem tailTrace_1545358 : CollatzResearch.WordTrace tailWord_1545358 prefixEnd_1545358 352671749898164450408015 := by
  unfold tailWord_1545358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7045479591929920872409591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37575891156959577986184485 7045479591929920872409591)
  ·
    refine ⟨10568219387894881308614387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7045479591929920872409591 10568219387894881308614387)
    ·
      refine ⟨15852329081842321962921581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10568219387894881308614387 15852329081842321962921581)
      ·
        refine ⟨5944623405690870736095593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15852329081842321962921581 5944623405690870736095593)
        ·
          refine ⟨4458467554268153052071695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5944623405690870736095593 4458467554268153052071695)
          ·
            refine ⟨6687701331402229578107543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4458467554268153052071695 6687701331402229578107543)
            ·
              refine ⟨10031551997103344367161315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6687701331402229578107543 10031551997103344367161315)
              ·
                refine ⟨15047327995655016550741973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10031551997103344367161315 15047327995655016550741973)
                ·
                  refine ⟨352671749898164450408015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15047327995655016550741973 352671749898164450408015)
                  ·
                    rfl

theorem cell21_1545358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1545358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545358 prefixEnd_1545358 := by exact prefixLift 1545358
  have htrace : WordTrace (prefixWord ++ tailWord_1545358) baseStart_1545358 baseEnd_1545358 := by
    simpa [prefixWord, tailWord_1545358, baseEnd_1545358] using wordTrace_append hprefix tailTrace_1545358
  have hstable : (prefixWord ++ tailWord_1545358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545358).length < 2 ^ (prefixWord ++ tailWord_1545358).sum := by decide
  have hdescent : baseEnd_1545358 < baseStart_1545358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545437 : List Nat := [1, 4, 3, 2, 3, 1, 7]
def baseStart_1545437 : Nat := 118140960795 + 1545437 * 2 ^ 59
def prefixEnd_1545437 : Nat := 4983230072969 + 3 ^ 40 * 1545437 * 2
def baseEnd_1545437 : Nat := 39187753197164207621243

theorem tailTrace_1545437 : CollatzResearch.WordTrace tailWord_1545437 prefixEnd_1545437 39187753197164207621243 := by
  unfold tailWord_1545437
  simp only [CollatzResearch.WordTrace]
  refine ⟨56366718102153163471402565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37577812068102108980935043 56366718102153163471402565)
  ·
    refine ⟨10568759644153718150887981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56366718102153163471402565 10568759644153718150887981)
    ·
      refine ⟨3963284866557644306582993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10568759644153718150887981 3963284866557644306582993)
      ·
        refine ⟨2972463649918233229937245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3963284866557644306582993 2972463649918233229937245)
        ·
          refine ⟨1114673868719337461226467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2972463649918233229937245 1114673868719337461226467)
          ·
            refine ⟨1672010803079006191839701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114673868719337461226467 1672010803079006191839701)
            ·
              refine ⟨39187753197164207621243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1672010803079006191839701 39187753197164207621243)
              ·
                rfl

theorem cell21_1545437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 7].length) (baseStart_1545437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545437 prefixEnd_1545437 := by exact prefixLift 1545437
  have htrace : WordTrace (prefixWord ++ tailWord_1545437) baseStart_1545437 baseEnd_1545437 := by
    simpa [prefixWord, tailWord_1545437, baseEnd_1545437] using wordTrace_append hprefix tailTrace_1545437
  have hstable : (prefixWord ++ tailWord_1545437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545437).length < 2 ^ (prefixWord ++ tailWord_1545437).sum := by decide
  have hdescent : baseEnd_1545437 < baseStart_1545437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545448 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_1545448 : Nat := 118140960795 + 1545448 * 2 ^ 59
def prefixEnd_1545448 : Nat := 4983230072969 + 3 ^ 40 * 1545448 * 2
def baseEnd_1545448 : Nat := 352692289124344293907831

theorem tailTrace_1545448 : CollatzResearch.WordTrace tailWord_1545448 prefixEnd_1545448 352692289124344293907831 := by
  unfold tailWord_1545448
  simp only [CollatzResearch.WordTrace]
  refine ⟨28183559652556656175026499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37578079536742208233368665 28183559652556656175026499)
  ·
    refine ⟨42275339478834984262539749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28183559652556656175026499 42275339478834984262539749)
    ·
      refine ⟨7926626152281559549226203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42275339478834984262539749 7926626152281559549226203)
      ·
        refine ⟨11889939228422339323839305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7926626152281559549226203 11889939228422339323839305)
        ·
          refine ⟨8917454421316754492879479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11889939228422339323839305 8917454421316754492879479)
          ·
            refine ⟨13376181631975131739319219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917454421316754492879479 13376181631975131739319219)
            ·
              refine ⟨20064272447962697608978829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13376181631975131739319219 20064272447962697608978829)
              ·
                refine ⟨7524102167986011603367061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20064272447962697608978829 7524102167986011603367061)
                ·
                  refine ⟨352692289124344293907831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7524102167986011603367061 352692289124344293907831)
                  ·
                    rfl

theorem cell21_1545448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_1545448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545448 prefixEnd_1545448 := by exact prefixLift 1545448
  have htrace : WordTrace (prefixWord ++ tailWord_1545448) baseStart_1545448 baseEnd_1545448 := by
    simpa [prefixWord, tailWord_1545448, baseEnd_1545448] using wordTrace_append hprefix tailTrace_1545448
  have hstable : (prefixWord ++ tailWord_1545448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545448).length < 2 ^ (prefixWord ++ tailWord_1545448).sum := by decide
  have hdescent : baseEnd_1545448 < baseStart_1545448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545589 : List Nat := [1, 3, 4, 1, 3, 2, 2, 5]
def baseStart_1545589 : Nat := 118140960795 + 1545589 * 2 ^ 59
def prefixEnd_1545589 : Nat := 4983230072969 + 3 ^ 40 * 1545589 * 2
def baseEnd_1545589 : Nat := 117574822415119794019181

theorem tailTrace_1545589 : CollatzResearch.WordTrace tailWord_1545589 prefixEnd_1545589 117574822415119794019181 := by
  unfold tailWord_1545589
  simp only [CollatzResearch.WordTrace]
  refine ⟨56372261997602493430935821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37581507998401662287290547 56372261997602493430935821)
  ·
    refine ⟨21139598249100935036600933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56372261997602493430935821 21139598249100935036600933)
    ·
      refine ⟨3963674671706425319362675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21139598249100935036600933 3963674671706425319362675)
      ·
        refine ⟨5945512007559637979044013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963674671706425319362675 5945512007559637979044013)
        ·
          refine ⟨2229567002834864242141505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5945512007559637979044013 2229567002834864242141505)
          ·
            refine ⟨1672175252126148181606129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229567002834864242141505 1672175252126148181606129)
            ·
              refine ⟨1254131439094611136204597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672175252126148181606129 1254131439094611136204597)
              ·
                refine ⟨117574822415119794019181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1254131439094611136204597 117574822415119794019181)
                ·
                  rfl

theorem cell21_1545589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 5].length) (baseStart_1545589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545589 prefixEnd_1545589 := by exact prefixLift 1545589
  have htrace : WordTrace (prefixWord ++ tailWord_1545589) baseStart_1545589 baseEnd_1545589 := by
    simpa [prefixWord, tailWord_1545589, baseEnd_1545589] using wordTrace_append hprefix tailTrace_1545589
  have hstable : (prefixWord ++ tailWord_1545589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545589).length < 2 ^ (prefixWord ++ tailWord_1545589).sum := by decide
  have hdescent : baseEnd_1545589 < baseStart_1545589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545603 : List Nat := [1, 1, 1, 3, 5, 1, 3, 3, 3]
def baseStart_1545603 : Nat := 118140960795 + 1545603 * 2 ^ 59
def prefixEnd_1545603 : Nat := 4983230072969 + 3 ^ 40 * 1545603 * 2
def baseEnd_1545603 : Nat := 352727662236098468824181

theorem tailTrace_1545603 : CollatzResearch.WordTrace tailWord_1545603 prefixEnd_1545603 352727662236098468824181 := by
  unfold tailWord_1545603
  simp only [CollatzResearch.WordTrace]
  refine ⟨56372772619551773821945463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37581848413034515881296975 56372772619551773821945463)
  ·
    refine ⟨84559158929327660732918195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56372772619551773821945463 84559158929327660732918195)
    ·
      refine ⟨126838738393991491099377293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84559158929327660732918195 126838738393991491099377293)
      ·
        refine ⟨47564526897746809162266485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126838738393991491099377293 47564526897746809162266485)
        ·
          refine ⟨4459174396663763358962483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47564526897746809162266485 4459174396663763358962483)
          ·
            refine ⟨6688761594995645038443725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459174396663763358962483 6688761594995645038443725)
            ·
              refine ⟨2508285598123366889416397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6688761594995645038443725 2508285598123366889416397)
              ·
                refine ⟨940607099296262583531149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2508285598123366889416397 940607099296262583531149)
                ·
                  refine ⟨352727662236098468824181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940607099296262583531149 352727662236098468824181)
                  ·
                    rfl

theorem cell21_1545603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 3].length) (baseStart_1545603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545603 prefixEnd_1545603 := by exact prefixLift 1545603
  have htrace : WordTrace (prefixWord ++ tailWord_1545603) baseStart_1545603 baseEnd_1545603 := by
    simpa [prefixWord, tailWord_1545603, baseEnd_1545603] using wordTrace_append hprefix tailTrace_1545603
  have hstable : (prefixWord ++ tailWord_1545603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545603).length < 2 ^ (prefixWord ++ tailWord_1545603).sum := by decide
  have hdescent : baseEnd_1545603 < baseStart_1545603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545631 : List Nat := [1, 1, 2, 5, 1, 3, 2, 6]
def baseStart_1545631 : Nat := 118140960795 + 1545631 * 2 ^ 59
def prefixEnd_1545631 : Nat := 4983230072969 + 3 ^ 40 * 1545631 * 2
def baseEnd_1545631 : Nat := 117578017405858880785819

theorem tailTrace_1545631 : CollatzResearch.WordTrace tailWord_1545631 prefixEnd_1545631 117578017405858880785819 := by
  unfold tailWord_1545631
  simp only [CollatzResearch.WordTrace]
  refine ⟨56373793863450334603964747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37582529242300223069309831 56373793863450334603964747)
  ·
    refine ⟨84560690795175501905947121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56373793863450334603964747 84560690795175501905947121)
    ·
      refine ⟨63420518096381626429460341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84560690795175501905947121 63420518096381626429460341)
      ·
        refine ⟨5945673571535777477761907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63420518096381626429460341 5945673571535777477761907)
        ·
          refine ⟨8918510357303666216642861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945673571535777477761907 8918510357303666216642861)
          ·
            refine ⟨3344441383988874831241073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8918510357303666216642861 3344441383988874831241073)
            ·
              refine ⟨2508331037991656123430805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3344441383988874831241073 2508331037991656123430805)
              ·
                refine ⟨117578017405858880785819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2508331037991656123430805 117578017405858880785819)
                ·
                  rfl

theorem cell21_1545631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 6].length) (baseStart_1545631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545631 prefixEnd_1545631 := by exact prefixLift 1545631
  have htrace : WordTrace (prefixWord ++ tailWord_1545631) baseStart_1545631 baseEnd_1545631 := by
    simpa [prefixWord, tailWord_1545631, baseEnd_1545631] using wordTrace_append hprefix tailTrace_1545631
  have hstable : (prefixWord ++ tailWord_1545631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545631).length < 2 ^ (prefixWord ++ tailWord_1545631).sum := by decide
  have hdescent : baseEnd_1545631 < baseStart_1545631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545634 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_1545634 : Nat := 118140960795 + 1545634 * 2 ^ 59
def prefixEnd_1545634 : Nat := 4983230072969 + 3 ^ 40 * 1545634 * 2
def baseEnd_1545634 : Nat := 352734736858449303807451

theorem tailTrace_1545634 : CollatzResearch.WordTrace tailWord_1545634 prefixEnd_1545634 352734736858449303807451 := by
  unfold tailWord_1545634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14093475820609866529080989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37582602188292977410882637 14093475820609866529080989)
  ·
    refine ⟨5285053432728699948405371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14093475820609866529080989 5285053432728699948405371)
    ·
      refine ⟨7927580149093049922608057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5285053432728699948405371 7927580149093049922608057)
      ·
        refine ⟨5945685111819787441956043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7927580149093049922608057 5945685111819787441956043)
        ·
          refine ⟨8918527667729681162934065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945685111819787441956043 8918527667729681162934065)
          ·
            refine ⟨6688895750797260872200549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8918527667729681162934065 6688895750797260872200549)
            ·
              refine ⟨1254167953274486413537603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6688895750797260872200549 1254167953274486413537603)
              ·
                refine ⟨1881251929911729620306405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254167953274486413537603 1881251929911729620306405)
                ·
                  refine ⟨352734736858449303807451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881251929911729620306405 352734736858449303807451)
                  ·
                    rfl

theorem cell21_1545634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_1545634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545634 prefixEnd_1545634 := by exact prefixLift 1545634
  have htrace : WordTrace (prefixWord ++ tailWord_1545634) baseStart_1545634 baseEnd_1545634 := by
    simpa [prefixWord, tailWord_1545634, baseEnd_1545634] using wordTrace_append hprefix tailTrace_1545634
  have hstable : (prefixWord ++ tailWord_1545634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545634).length < 2 ^ (prefixWord ++ tailWord_1545634).sum := by decide
  have hdescent : baseEnd_1545634 < baseStart_1545634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545679 : List Nat := [1, 1, 2, 1, 1, 4, 6, 2, 3]
def baseStart_1545679 : Nat := 118140960795 + 1545679 * 2 ^ 59
def prefixEnd_1545679 : Nat := 4983230072969 + 3 ^ 40 * 1545679 * 2
def baseEnd_1545679 : Nat := 352745006471539225557359

theorem tailTrace_1545679 : CollatzResearch.WordTrace tailWord_1545679 prefixEnd_1545679 352745006471539225557359 := by
  unfold tailWord_1545679
  simp only [CollatzResearch.WordTrace]
  refine ⟨56375544567276438801712091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37583696378184292534474727 56375544567276438801712091)
  ·
    refine ⟨84563316850914658202568137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56375544567276438801712091 84563316850914658202568137)
    ·
      refine ⟨63422487638185993651926103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84563316850914658202568137 63422487638185993651926103)
      ·
        refine ⟨95133731457278990477889155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63422487638185993651926103 95133731457278990477889155)
        ·
          refine ⟨142700597185918485716833733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95133731457278990477889155 142700597185918485716833733)
          ·
            refine ⟨26756361972359716071906325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142700597185918485716833733 26756361972359716071906325)
            ·
              refine ⟨1254204467454361690870609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26756361972359716071906325 1254204467454361690870609)
              ·
                refine ⟨940653350590771268152957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1254204467454361690870609 940653350590771268152957)
                ·
                  refine ⟨352745006471539225557359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940653350590771268152957 352745006471539225557359)
                  ·
                    rfl

theorem cell21_1545679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 3].length) (baseStart_1545679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545679 prefixEnd_1545679 := by exact prefixLift 1545679
  have htrace : WordTrace (prefixWord ++ tailWord_1545679) baseStart_1545679 baseEnd_1545679 := by
    simpa [prefixWord, tailWord_1545679, baseEnd_1545679] using wordTrace_append hprefix tailTrace_1545679
  have hstable : (prefixWord ++ tailWord_1545679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545679).length < 2 ^ (prefixWord ++ tailWord_1545679).sum := by decide
  have hdescent : baseEnd_1545679 < baseStart_1545679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545693 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1545693 : Nat := 118140960795 + 1545693 * 2 ^ 59
def prefixEnd_1545693 : Nat := 4983230072969 + 3 ^ 40 * 1545693 * 2
def baseEnd_1545693 : Nat := 352748201462278312323997

theorem tailTrace_1545693 : CollatzResearch.WordTrace tailWord_1545693 prefixEnd_1545693 352748201462278312323997 := by
  unfold tailWord_1545693
  simp only [CollatzResearch.WordTrace]
  refine ⟨56376055189225719192721733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37584036792817146128481155 56376055189225719192721733)
  ·
    refine ⟨10570510347979822348635325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56376055189225719192721733 10570510347979822348635325)
    ·
      refine ⟨3963941380492433380738247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10570510347979822348635325 3963941380492433380738247)
      ·
        refine ⟨5945912070738650071107371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963941380492433380738247 5945912070738650071107371)
        ·
          refine ⟨8918868106107975106661057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945912070738650071107371 8918868106107975106661057)
          ·
            refine ⟨6689151079580981329995793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8918868106107975106661057 6689151079580981329995793)
            ·
              refine ⟨5016863309685735997496845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6689151079580981329995793 5016863309685735997496845)
              ·
                refine ⟨1881323741132150999061317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5016863309685735997496845 1881323741132150999061317)
                ·
                  refine ⟨352748201462278312323997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881323741132150999061317 352748201462278312323997)
                  ·
                    rfl

theorem cell21_1545693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1545693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545693 prefixEnd_1545693 := by exact prefixLift 1545693
  have htrace : WordTrace (prefixWord ++ tailWord_1545693) baseStart_1545693 baseEnd_1545693 := by
    simpa [prefixWord, tailWord_1545693, baseEnd_1545693] using wordTrace_append hprefix tailTrace_1545693
  have hstable : (prefixWord ++ tailWord_1545693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545693).length < 2 ^ (prefixWord ++ tailWord_1545693).sum := by decide
  have hdescent : baseEnd_1545693 < baseStart_1545693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545738 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_1545738 : Nat := 118140960795 + 1545738 * 2 ^ 59
def prefixEnd_1545738 : Nat := 4983230072969 + 3 ^ 40 * 1545738 * 2
def baseEnd_1545738 : Nat := 352758471075368234073905

theorem tailTrace_1545738 : CollatzResearch.WordTrace tailWord_1545738 prefixEnd_1545738 352758471075368234073905 := by
  unfold tailWord_1545738
  simp only [CollatzResearch.WordTrace]
  refine ⟨14094424118515672969527467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37585130982708461252073245 14094424118515672969527467)
  ·
    refine ⟨21141636177773509454291201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14094424118515672969527467 21141636177773509454291201)
    ·
      refine ⟨15856227133330132090718401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21141636177773509454291201 15856227133330132090718401)
      ·
        refine ⟨11892170349997599068038801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15856227133330132090718401 11892170349997599068038801)
        ·
          refine ⟨8919127762498199301029101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11892170349997599068038801 8919127762498199301029101)
          ·
            refine ⟨3344672910936824737885913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8919127762498199301029101 3344672910936824737885913)
            ·
              refine ⟨2508504683202618553414435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3344672910936824737885913 2508504683202618553414435)
              ·
                refine ⟨3762757024803927830121653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508504683202618553414435 3762757024803927830121653)
                ·
                  refine ⟨352758471075368234073905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3762757024803927830121653 352758471075368234073905)
                  ·
                    rfl

theorem cell21_1545738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_1545738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545738 prefixEnd_1545738 := by exact prefixLift 1545738
  have htrace : WordTrace (prefixWord ++ tailWord_1545738) baseStart_1545738 baseEnd_1545738 := by
    simpa [prefixWord, tailWord_1545738, baseEnd_1545738] using wordTrace_append hprefix tailTrace_1545738
  have hstable : (prefixWord ++ tailWord_1545738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545738).length < 2 ^ (prefixWord ++ tailWord_1545738).sum := by decide
  have hdescent : baseEnd_1545738 < baseStart_1545738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545758 : List Nat := [4, 3, 3, 1, 1, 1, 1, 7]
def baseStart_1545758 : Nat := 118140960795 + 1545758 * 2 ^ 59
def prefixEnd_1545758 : Nat := 4983230072969 + 3 ^ 40 * 1545758 * 2
def baseEnd_1545758 : Nat := 117587678449284214580177

theorem tailTrace_1545758 : CollatzResearch.WordTrace tailWord_1545758 prefixEnd_1545758 117587678449284214580177 := by
  unfold tailWord_1545758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047303241748779411729741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37585617289326823529225285 7047303241748779411729741)
  ·
    refine ⟨2642738715655792279398653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7047303241748779411729741 2642738715655792279398653)
    ·
      refine ⟨991027018370922104774495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2642738715655792279398653 991027018370922104774495)
      ·
        refine ⟨1486540527556383157161743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991027018370922104774495 1486540527556383157161743)
        ·
          refine ⟨2229810791334574735742615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486540527556383157161743 2229810791334574735742615)
          ·
            refine ⟨3344716187001862103613923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229810791334574735742615 3344716187001862103613923)
            ·
              refine ⟨5017074280502793155420885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344716187001862103613923 5017074280502793155420885)
              ·
                refine ⟨117587678449284214580177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5017074280502793155420885 117587678449284214580177)
                ·
                  rfl

theorem cell21_1545758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_1545758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545758 prefixEnd_1545758 := by exact prefixLift 1545758
  have htrace : WordTrace (prefixWord ++ tailWord_1545758) baseStart_1545758 baseEnd_1545758 := by
    simpa [prefixWord, tailWord_1545758, baseEnd_1545758] using wordTrace_append hprefix tailTrace_1545758
  have hstable : (prefixWord ++ tailWord_1545758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545758).length < 2 ^ (prefixWord ++ tailWord_1545758).sum := by decide
  have hdescent : baseEnd_1545758 < baseStart_1545758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545842 : List Nat := [3, 2, 1, 2, 3, 10]
def baseStart_1545842 : Nat := 118140960795 + 1545842 * 2 ^ 59
def prefixEnd_1545842 : Nat := 4983230072969 + 3 ^ 40 * 1545842 * 2
def baseEnd_1545842 : Nat := 13066007603418043123717

theorem tailTrace_1545842 : CollatzResearch.WordTrace tailWord_1545842 prefixEnd_1545842 13066007603418043123717 := by
  unfold tailWord_1545842
  simp only [CollatzResearch.WordTrace]
  refine ⟨14095372416421479409973945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37587659777123945093263853 14095372416421479409973945)
  ·
    refine ⟨10571529312316109557480459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14095372416421479409973945 10571529312316109557480459)
    ·
      refine ⟨15857293968474164336220689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10571529312316109557480459 15857293968474164336220689)
      ·
        refine ⟨11892970476355623252165517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15857293968474164336220689 11892970476355623252165517)
        ·
          refine ⟨4459863928633358719562069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11892970476355623252165517 4459863928633358719562069)
          ·
            refine ⟨13066007603418043123717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4459863928633358719562069 13066007603418043123717)
            ·
              rfl

theorem cell21_1545842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 10].length) (baseStart_1545842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545842 prefixEnd_1545842 := by exact prefixLift 1545842
  have htrace : WordTrace (prefixWord ++ tailWord_1545842) baseStart_1545842 baseEnd_1545842 := by
    simpa [prefixWord, tailWord_1545842, baseEnd_1545842] using wordTrace_append hprefix tailTrace_1545842
  have hstable : (prefixWord ++ tailWord_1545842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545842).length < 2 ^ (prefixWord ++ tailWord_1545842).sum := by decide
  have hdescent : baseEnd_1545842 < baseStart_1545842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545845 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 4]
def baseStart_1545845 : Nat := 118140960795 + 1545845 * 2 ^ 59
def prefixEnd_1545845 : Nat := 4983230072969 + 3 ^ 40 * 1545845 * 2
def baseEnd_1545845 : Nat := 352782889933159825790353

theorem tailTrace_1545845 : CollatzResearch.WordTrace tailWord_1545845 prefixEnd_1545845 352782889933159825790353 := by
  unfold tailWord_1545845
  simp only [CollatzResearch.WordTrace]
  refine ⟨56381599084675049152254989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37587732723116699434836659 56381599084675049152254989)
  ·
    refine ⟨21143099656753143432095621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56381599084675049152254989 21143099656753143432095621)
    ·
      refine ⟨3964331185641214393517929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21143099656753143432095621 3964331185641214393517929)
      ·
        refine ⟨2973248389230910795138447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3964331185641214393517929 2973248389230910795138447)
        ·
          refine ⟨4459872583846366192707671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2973248389230910795138447 4459872583846366192707671)
          ·
            refine ⟨6689808875769549289061507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459872583846366192707671 6689808875769549289061507)
            ·
              refine ⟨10034713313654323933592261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689808875769549289061507 10034713313654323933592261)
              ·
                refine ⟨1881508746310185737548549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10034713313654323933592261 1881508746310185737548549)
                ·
                  refine ⟨352782889933159825790353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881508746310185737548549 352782889933159825790353)
                  ·
                    rfl

theorem cell21_1545845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_1545845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545845 prefixEnd_1545845 := by exact prefixLift 1545845
  have htrace : WordTrace (prefixWord ++ tailWord_1545845) baseStart_1545845 baseEnd_1545845 := by
    simpa [prefixWord, tailWord_1545845, baseEnd_1545845] using wordTrace_append hprefix tailTrace_1545845
  have hstable : (prefixWord ++ tailWord_1545845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545845).length < 2 ^ (prefixWord ++ tailWord_1545845).sum := by decide
  have hdescent : baseEnd_1545845 < baseStart_1545845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545896 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 4]
def baseStart_1545896 : Nat := 118140960795 + 1545896 * 2 ^ 59
def prefixEnd_1545896 : Nat := 4983230072969 + 3 ^ 40 * 1545896 * 2
def baseEnd_1545896 : Nat := 352794528827995070440249

theorem tailTrace_1545896 : CollatzResearch.WordTrace tailWord_1545896 prefixEnd_1545896 352794528827995070440249 := by
  unfold tailWord_1545896
  simp only [CollatzResearch.WordTrace]
  refine ⟨28191729603745142431180771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37588972804993523241574361 28191729603745142431180771)
  ·
    refine ⟨42287594405617713646771157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28191729603745142431180771 42287594405617713646771157)
    ·
      refine ⟨991115493881665163596199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42287594405617713646771157 991115493881665163596199)
      ·
        refine ⟨1486673240822497745394299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991115493881665163596199 1486673240822497745394299)
        ·
          refine ⟨2230009861233746618091449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486673240822497745394299 2230009861233746618091449)
          ·
            refine ⟨1672507395925309963568587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230009861233746618091449 1672507395925309963568587)
            ·
              refine ⟨2508761093887964945352881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672507395925309963568587 2508761093887964945352881)
              ·
                refine ⟨1881570820415973709014661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508761093887964945352881 1881570820415973709014661)
                ·
                  refine ⟨352794528827995070440249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881570820415973709014661 352794528827995070440249)
                  ·
                    rfl

theorem cell21_1545896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 4].length) (baseStart_1545896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545896 prefixEnd_1545896 := by exact prefixLift 1545896
  have htrace : WordTrace (prefixWord ++ tailWord_1545896) baseStart_1545896 baseEnd_1545896 := by
    simpa [prefixWord, tailWord_1545896, baseEnd_1545896] using wordTrace_append hprefix tailTrace_1545896
  have hstable : (prefixWord ++ tailWord_1545896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545896).length < 2 ^ (prefixWord ++ tailWord_1545896).sum := by decide
  have hdescent : baseEnd_1545896 < baseStart_1545896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545904 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_1545904 : Nat := 118140960795 + 1545904 * 2 ^ 59
def prefixEnd_1545904 : Nat := 4983230072969 + 3 ^ 40 * 1545904 * 2
def baseEnd_1545904 : Nat := 352796354536988834306899

theorem tailTrace_1545904 : CollatzResearch.WordTrace tailWord_1545904 prefixEnd_1545904 352796354536988834306899 := by
  unfold tailWord_1545904
  simp only [CollatzResearch.WordTrace]
  refine ⟨28191875495730651114326383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37589167327640868152435177 28191875495730651114326383)
  ·
    refine ⟨42287813243595976671489575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28191875495730651114326383 42287813243595976671489575)
    ·
      refine ⟨63431719865393965007234363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42287813243595976671489575 63431719865393965007234363)
      ·
        refine ⟨95147579798090947510851545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63431719865393965007234363 95147579798090947510851545)
        ·
          refine ⟨71360684848568210633138659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95147579798090947510851545 71360684848568210633138659)
          ·
            refine ⟨107041027272852315949707989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71360684848568210633138659 107041027272852315949707989)
            ·
              refine ⟨2508774076707476155071281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 107041027272852315949707989 2508774076707476155071281)
              ·
                refine ⟨1881580557530607116303461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508774076707476155071281 1881580557530607116303461)
                ·
                  refine ⟨352796354536988834306899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881580557530607116303461 352796354536988834306899)
                  ·
                    rfl

theorem cell21_1545904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_1545904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545904 prefixEnd_1545904 := by exact prefixLift 1545904
  have htrace : WordTrace (prefixWord ++ tailWord_1545904) baseStart_1545904 baseEnd_1545904 := by
    simpa [prefixWord, tailWord_1545904, baseEnd_1545904] using wordTrace_append hprefix tailTrace_1545904
  have hstable : (prefixWord ++ tailWord_1545904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545904).length < 2 ^ (prefixWord ++ tailWord_1545904).sum := by decide
  have hdescent : baseEnd_1545904 < baseStart_1545904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545963 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 6]
def baseStart_1545963 : Nat := 118140960795 + 1545963 * 2 ^ 59
def prefixEnd_1545963 : Nat := 4983230072969 + 3 ^ 40 * 1545963 * 2
def baseEnd_1545963 : Nat := 352809819140817842823445

theorem tailTrace_1545963 : CollatzResearch.WordTrace tailWord_1545963 prefixEnd_1545963 352809819140817842823445 := by
  unfold tailWord_1545963
  simp only [CollatzResearch.WordTrace]
  refine ⟨56385902898247555305050543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37590601932165036870033695 56385902898247555305050543)
  ·
    refine ⟨84578854347371332957575815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56385902898247555305050543 84578854347371332957575815)
    ·
      refine ⟨126868281521056999436363723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84578854347371332957575815 126868281521056999436363723)
      ·
        refine ⟨190302422281585499154545585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126868281521056999436363723 190302422281585499154545585)
        ·
          refine ⟨142726816711189124365909189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190302422281585499154545585 142726816711189124365909189)
          ·
            refine ⟨26761278133347960818607973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142726816711189124365909189 26761278133347960818607973)
            ·
              refine ⟨5017739650002742653488995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26761278133347960818607973 5017739650002742653488995)
              ·
                refine ⟨7526609475004113980233493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017739650002742653488995 7526609475004113980233493)
                ·
                  refine ⟨352809819140817842823445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7526609475004113980233493 352809819140817842823445)
                  ·
                    rfl

theorem cell21_1545963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_1545963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545963 prefixEnd_1545963 := by exact prefixLift 1545963
  have htrace : WordTrace (prefixWord ++ tailWord_1545963) baseStart_1545963 baseEnd_1545963 := by
    simpa [prefixWord, tailWord_1545963, baseEnd_1545963] using wordTrace_append hprefix tailTrace_1545963
  have hstable : (prefixWord ++ tailWord_1545963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545963).length < 2 ^ (prefixWord ++ tailWord_1545963).sum := by decide
  have hdescent : baseEnd_1545963 < baseStart_1545963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545972 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1545972 : Nat := 118140960795 + 1545972 * 2 ^ 59
def prefixEnd_1545972 : Nat := 4983230072969 + 3 ^ 40 * 1545972 * 2
def baseEnd_1545972 : Nat := 352811873063435827173427

theorem tailTrace_1545972 : CollatzResearch.WordTrace tailWord_1545972 prefixEnd_1545972 352811873063435827173427 := by
  unfold tailWord_1545972
  simp only [CollatzResearch.WordTrace]
  refine ⟨28193115577607474921064085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37590820770143299894752113 28193115577607474921064085)
  ·
    refine ⟨1321552292700350386924879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28193115577607474921064085 1321552292700350386924879)
    ·
      refine ⟨1982328439050525580387319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1321552292700350386924879 1982328439050525580387319)
      ·
        refine ⟨2973492658575788370580979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982328439050525580387319 2973492658575788370580979)
        ·
          refine ⟨4460238987863682555871469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2973492658575788370580979 4460238987863682555871469)
          ·
            refine ⟨1672589620448880958451801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4460238987863682555871469 1672589620448880958451801)
            ·
              refine ⟨1254442215336660718838851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672589620448880958451801 1254442215336660718838851)
              ·
                refine ⟨1881663323004991078258277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254442215336660718838851 1881663323004991078258277)
                ·
                  refine ⟨352811873063435827173427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881663323004991078258277 352811873063435827173427)
                  ·
                    rfl

theorem cell21_1545972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1545972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545972 prefixEnd_1545972 := by exact prefixLift 1545972
  have htrace : WordTrace (prefixWord ++ tailWord_1545972) baseStart_1545972 baseEnd_1545972 := by
    simpa [prefixWord, tailWord_1545972, baseEnd_1545972] using wordTrace_append hprefix tailTrace_1545972
  have hstable : (prefixWord ++ tailWord_1545972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545972).length < 2 ^ (prefixWord ++ tailWord_1545972).sum := by decide
  have hdescent : baseEnd_1545972 < baseStart_1545972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545980 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_1545980 : Nat := 118140960795 + 1545980 * 2 ^ 59
def prefixEnd_1545980 : Nat := 4983230072969 + 3 ^ 40 * 1545980 * 2
def baseEnd_1545980 : Nat := 352813698772429591040077

theorem tailTrace_1545980 : CollatzResearch.WordTrace tailWord_1545980 prefixEnd_1545980 352813698772429591040077 := by
  unfold tailWord_1545980
  simp only [CollatzResearch.WordTrace]
  refine ⟨28193261469592983604209697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37591015292790644805612929 28193261469592983604209697)
  ·
    refine ⟨21144946102194737703157273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28193261469592983604209697 21144946102194737703157273)
    ·
      refine ⟨15858709576646053277367955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21144946102194737703157273 15858709576646053277367955)
      ·
        refine ⟨23788064364969079916051933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15858709576646053277367955 23788064364969079916051933)
        ·
          refine ⟨8920524136863404968519475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23788064364969079916051933 8920524136863404968519475)
          ·
            refine ⟨13380786205295107452779213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8920524136863404968519475 13380786205295107452779213)
            ·
              refine ⟨5017794826985665294792205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13380786205295107452779213 5017794826985665294792205)
              ·
                refine ⟨1881673060119624485547077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5017794826985665294792205 1881673060119624485547077)
                ·
                  refine ⟨352813698772429591040077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881673060119624485547077 352813698772429591040077)
                  ·
                    rfl

theorem cell21_1545980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_1545980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545980 prefixEnd_1545980 := by exact prefixLift 1545980
  have htrace : WordTrace (prefixWord ++ tailWord_1545980) baseStart_1545980 baseEnd_1545980 := by
    simpa [prefixWord, tailWord_1545980, baseEnd_1545980] using wordTrace_append hprefix tailTrace_1545980
  have hstable : (prefixWord ++ tailWord_1545980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545980).length < 2 ^ (prefixWord ++ tailWord_1545980).sum := by decide
  have hdescent : baseEnd_1545980 < baseStart_1545980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545994 : List Nat := [3, 1, 2, 2, 1, 3, 2, 7]
def baseStart_1545994 : Nat := 118140960795 + 1545994 * 2 ^ 59
def prefixEnd_1545994 : Nat := 4983230072969 + 3 ^ 40 * 1545994 * 2
def baseEnd_1545994 : Nat := 117605631254389559268905

theorem tailTrace_1545994 : CollatzResearch.WordTrace tailWord_1545994 prefixEnd_1545994 117605631254389559268905 := by
  unfold tailWord_1545994
  simp only [CollatzResearch.WordTrace]
  refine ⟨14096758390283811899857259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37591355707423498399619357 14096758390283811899857259)
  ·
    refine ⟨21145137585425717849785889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14096758390283811899857259 21145137585425717849785889)
    ·
      refine ⟨15858853189069288387339417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21145137585425717849785889 15858853189069288387339417)
      ·
        refine ⟨11894139891801966290504563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15858853189069288387339417 11894139891801966290504563)
        ·
          refine ⟨17841209837702949435756845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11894139891801966290504563 17841209837702949435756845)
          ·
            refine ⟨6690453689138606038408817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17841209837702949435756845 6690453689138606038408817)
            ·
              refine ⟨5017840266853954528806613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6690453689138606038408817 5017840266853954528806613)
              ·
                refine ⟨117605631254389559268905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5017840266853954528806613 117605631254389559268905)
                ·
                  rfl

theorem cell21_1545994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_1545994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1545994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1545994 prefixEnd_1545994 := by exact prefixLift 1545994
  have htrace : WordTrace (prefixWord ++ tailWord_1545994) baseStart_1545994 baseEnd_1545994 := by
    simpa [prefixWord, tailWord_1545994, baseEnd_1545994] using wordTrace_append hprefix tailTrace_1545994
  have hstable : (prefixWord ++ tailWord_1545994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545994).length < 2 ^ (prefixWord ++ tailWord_1545994).sum := by decide
  have hdescent : baseEnd_1545994 < baseStart_1545994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546101 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 5]
def baseStart_1546101 : Nat := 118140960795 + 1546101 * 2 ^ 59
def prefixEnd_1546101 : Nat := 4983230072969 + 3 ^ 40 * 1546101 * 2
def baseEnd_1546101 : Nat := 352841312620960269523163

theorem tailTrace_1546101 : CollatzResearch.WordTrace tailWord_1546101 prefixEnd_1546101 352841312620960269523163 := by
  unfold tailWord_1546101
  simp only [CollatzResearch.WordTrace]
  refine ⟨56390936171747604873574157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37593957447831736582382771 56390936171747604873574157)
  ·
    refine ⟨21146601064405351827590309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56390936171747604873574157 21146601064405351827590309)
    ·
      refine ⟨3964987699576003467673183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21146601064405351827590309 3964987699576003467673183)
      ·
        refine ⟨5947481549364005201509775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3964987699576003467673183 5947481549364005201509775)
        ·
          refine ⟨8921222324046007802264663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5947481549364005201509775 8921222324046007802264663)
          ·
            refine ⟨13381833486069011703396995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8921222324046007802264663 13381833486069011703396995)
            ·
              refine ⟨20072750229103517555095493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13381833486069011703396995 20072750229103517555095493)
              ·
                refine ⟨3763640667956909541580405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20072750229103517555095493 3763640667956909541580405)
                ·
                  refine ⟨352841312620960269523163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3763640667956909541580405 352841312620960269523163)
                  ·
                    rfl

theorem cell21_1546101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_1546101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546101 prefixEnd_1546101 := by exact prefixLift 1546101
  have htrace : WordTrace (prefixWord ++ tailWord_1546101) baseStart_1546101 baseEnd_1546101 := by
    simpa [prefixWord, tailWord_1546101, baseEnd_1546101] using wordTrace_append hprefix tailTrace_1546101
  have hstable : (prefixWord ++ tailWord_1546101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546101).length < 2 ^ (prefixWord ++ tailWord_1546101).sum := by decide
  have hdescent : baseEnd_1546101 < baseStart_1546101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546115 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 6]
def baseStart_1546115 : Nat := 118140960795 + 1546115 * 2 ^ 59
def prefixEnd_1546115 : Nat := 4983230072969 + 3 ^ 40 * 1546115 * 2
def baseEnd_1546115 : Nat := 352844507611699356289801

theorem tailTrace_1546115 : CollatzResearch.WordTrace tailWord_1546115 prefixEnd_1546115 352844507611699356289801 := by
  unfold tailWord_1546115
  simp only [CollatzResearch.WordTrace]
  refine ⟨56391446793696885264583799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37594297862464590176389199 56391446793696885264583799)
  ·
    refine ⟨84587170190545327896875699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56391446793696885264583799 84587170190545327896875699)
    ·
      refine ⟨126880755285817991845313549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84587170190545327896875699 126880755285817991845313549)
      ·
        refine ⟨47580283232181746941992581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126880755285817991845313549 47580283232181746941992581)
        ·
          refine ⟨8921303106034077551623609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47580283232181746941992581 8921303106034077551623609)
          ·
            refine ⟨6690977329525558163717707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8921303106034077551623609 6690977329525558163717707)
            ·
              refine ⟨10036465994288337245576561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690977329525558163717707 10036465994288337245576561)
              ·
                refine ⟨7527349495716252934182421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10036465994288337245576561 7527349495716252934182421)
                ·
                  refine ⟨352844507611699356289801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7527349495716252934182421 352844507611699356289801)
                  ·
                    rfl

theorem cell21_1546115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_1546115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546115 prefixEnd_1546115 := by exact prefixLift 1546115
  have htrace : WordTrace (prefixWord ++ tailWord_1546115) baseStart_1546115 baseEnd_1546115 := by
    simpa [prefixWord, tailWord_1546115, baseEnd_1546115] using wordTrace_append hprefix tailTrace_1546115
  have hstable : (prefixWord ++ tailWord_1546115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546115).length < 2 ^ (prefixWord ++ tailWord_1546115).sum := by decide
  have hdescent : baseEnd_1546115 < baseStart_1546115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
